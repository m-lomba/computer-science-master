/*  ****************** Signatures and Facts ******************   */

sig Topic{}

sig Producer{}

var sig Message{
  var t : Topic,
  var p : Producer
}{
  some p : Partition | this in p.msg
}

// The set of messages can change, because a message disappears if it is stored in a single (non-replicated) partition,
// and the partition disappears because the broker that hosts it fails.
// For this reason, we make signature Message mutable.
// Hence, we make the fields of Message mutable, because the domains of the relationships can change.
// However, we need to say that the value of the fields does not change over time, which is the property captured by the next constraint.
fact messageImmutableUnlessDisappear {
  always all m:Message | ( not m in Message' )
                                        or
                                        ( m.t = m.t'  and m.p = m.p' )
}

sig Consumer{
  var recmsg : set Message
}

var sig Broker{
  var parts : some Partition
}{
  one c : Cluster | this in c.brokers
  // this next constraint might be removed if we allow partitions to be replicated on the same broker
  no disj p1, p2 : parts | some rp : ReplicatedPartition | p1 + p2 in rp.(foll + leader)
}

// A broker can fail, hence disappear. For this reason, signature Broker is mutable.
// Then, like for the fields of Message, field "parts" of Broker is mutable because the domain (the signature) is mutable.
// We need to say that the field does not change, however, unless the broker fails (in which case it disappears)
fact brokersImmutableUnlessFail {
  always all b:Broker | ( not b in Broker' )
                                   or
                                   b.parts' = b.parts
}


sig Cluster{
  var brokers : some Broker
}


var sig Partition{
  var msg : some Message,
  var t : Topic
}{
  // the topic of the partition must correspond to the topic of its messages (which must all be the same)
  all m: msg | m.t = t
  // A partition belongs to exactly one broker 
  one b : Broker | this in b.parts
}

// A partition can disappear, when the broker that hosts it fails. Hence, signature Partition is mutable,
// and so are its fields, because the domain (the signature) is mutable.
// We need to say that the field capturing the topic does not change, however, unless the partition disappears.
// in addition, messages cannot disappear from the partition, but they can be added.
fact partitionImmutableUnlessDisappear {
  always all p:Partition | ( not p in Partition' )
                                      or
                                      ( p.t' = p.t and p.msg in p.msg' )
}

// This signature is introduced to separate leading partition from following ones.
// Notice that each partition is associated with exactly one broker, so saying that a partition is a leader is like saying that the corresponding broker is a leader.
sig ReplicatedPartition{
  var leader : Partition,
  var foll : set Partition
}{ 
  // a partition cannot be both leader and follower
  leader & foll = none
  // all partitions that are replica of one another have the same topic
  all f : foll | f.t = leader.t
  // this is a constraint that derives from the fact that we can have several clusters
  // and we need to assert that there cannot be replicated partitions shared across clusters
  no disj b1, b2: Broker, disj c1, c2: Cluster |
                b1 in c1.brokers and b2 in c2.brokers and 
                (foll + leader) & b1.parts != none and 
                (foll + leader) & b2.parts != none
  // if the leading partition does not disappear (because the corresponding broker disappears),
  // the leader does not change
  leader in Partition' implies leader' = leader
  // a follower, unless it disappears, remains in the set of replicas
  // on the other hand, it can change its nature, from follwer to leader (if the leader disappears,
  // it needs to be replaced)
  all f : foll | f in Partition' implies f in (foll'+leader')
  // partitions cannot be added to the set of replicas, they can only be removed
  (foll'+leader') in foll+leader
  // followers cannot have more messages than the leader; on the other hand, it is possible
  // that a follower has LESS messages than the leader, when the leader receives a new message
  all f : foll | f.msg in leader.msg
}

// Initially all replicas of the same partition have the same messages.
// This is not always true, because when new messages are stored in the cluster, they are stored
// first in the partition of the leading broker, and then in all the others.
// The constraint is in a separate fact and not in an implicit contraint in the signature because those constraints are 
// implicitly temporally quantified with an "always"
fact initiallyReplicatedEqual{
  all rp : ReplicatedPartition, p1, p2 : rp.(leader+foll) | p1.msg = p2.msg
}

// Messages do not appear in multiple partitions, unless the partitions are replicas of one another
fact messageNotDuplicated {
  always all m : Message, disj p1, p2 : Partition | m in p1.msg & p2.msg
                                                                            implies 
                                                                            some rp: ReplicatedPartition | p1+p2 in rp.(leader+foll)
}

// Different sets of replicated partitions include different partitions
fact disjointReplicatedPartitions{
  always all disj rp1, rp2 : ReplicatedPartition | rp1.(leader+ foll) & rp2.(leader+ foll) = none
}


/*  ****************** Part 1 ******************   */

// This is just a support predicate to ease the writing of predicate show;
// it says that the broker hosts 2 partitions on different topics
pred brokerProp [ b : Broker]{
  some disj p1, p2 : Partition | p1 in b.parts and p1 in b.parts and p1.t != p2.t
}

pred show{
  some disj b1, b2 : Broker | brokerProp[b1] and brokerProp[b2]
  // we need to make sure that there at least one follower to show the distribution of the message
  some rp : ReplicatedPartition | rp.foll != none
}

run show for 5 but 1 Cluster


/*  ****************** Part 2 ******************   */

fact messageDistribution{
  after always
    all m: Message | 
                              // the message is new, it was not part of the messages previously
                              before not (m in Message)
                              implies
                              some p : Partition |
                                     m.t = p.t and
                                     m in p.msg and
                                     ( // there is also the possiblity that the message is added to a partition that is not replicated
                                       p not in ReplicatedPartition.(leader+foll)
                                       or
                                       // if it added to a replicated partition, that partition is the leading partition
                                       some rp : ReplicatedPartition | p in rp.leader and 
                                                                                        // then the message is added also to the followers
                                                                                        all p1 : rp.foll | (not m in p1.msg) and m in p1.msg' )
                                       
}

// this is just a support predicate to make it easier to express show2
// it simply captures the property that message m is added to partition p
pred newMsg[m : Message, p : Partition]{
  before not (m in Message) and 
  m in p.msg and
  some rp : ReplicatedPartition | p in rp.(leader+foll) and rp.foll != none
}

pred show2{
  after ( some m1 : Message, p1 : Partition | newMsg[m1,p1] and 
                                                                     ( after some m2 : Message, p2 : Partition | m2.t != m1.t and newMsg[m2, p2] ))
  // for simplicity, we do not have that borkers can disappear in this case
  always(brokers' = brokers)
}

run show2 for 5 but 1 Cluster


/*  ****************** Part 3 ******************   */

// We do not need to add anything new to capture the fact that brokers can fail and, in case they do,
// new leaders must be selected for the set of replicated partitions that they lead.
// All this is guaranteed already by the constraints on ReplicatedPartition

pred show3{
  ( always Broker' in Broker )
  eventually (some b:Broker | not b in Broker' and 
                                              some p : b.parts, rp : ReplicatedPartition | p in rp.leader and rp.foll != none )
}

run show3 for 5 but 1 Cluster

assert leaderUnchanged {
  always all rp : ReplicatedPartition | rp.leader = rp.leader'
}

check leaderUnchanged for 5 but 1 Cluster
