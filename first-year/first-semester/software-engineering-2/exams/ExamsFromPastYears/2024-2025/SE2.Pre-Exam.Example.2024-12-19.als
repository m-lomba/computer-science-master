//////////////////   SIGNATURES  /////////////////////////////
enum bool {true, false}


abstract sig NetworkElement {}


sig Intersection extends NetworkElement {
  // this is to be added by STEP 3
  var hasAccident : bool
}{ some r : Road | this in r.orig }


sig Road extends NetworkElement {
  orig: Intersection,
  dest: Intersection  
}{ not orig = dest }


sig Vehicle {
  // this var is the thing to be added in STEP 2 (pos is already introduced in STEP 1)
  var pos : NetworkElement
}


//////////////////   STEP 1  /////////////////////////////

fact noTwoSameRoads {
  no disj r1, r2 : Road | r1.orig = r2.orig and r1.dest = r2.dest
}



pred show {
  // there is a 2-way street
  some i1, i2: Intersection, r1, r2 : Road | r1.orig = i1 and r1.dest = i2 and r2.orig = i2 and r2.dest = i1
  // there is a 1-way street
  some i1, i2: Intersection, r1: Road | r1.orig = i1 and r1.dest = i2 and 
                                                          no r2 : Road | r2.orig = i2 and r2.dest = i1
  some ne : NetworkElement | #ne.~pos > 1
}

run show for 5 but 10 NetworkElement




/////////////////// STEP 2  /////////////////////////////
// Facts 


fact carMovement {
  always all v : Vehicle | not (v.pos = v.pos') implies
                                           (v.pos in Road and v.pos' = v.pos.dest)
                                           or
                                           (v.pos in Intersection and v.pos' in v.pos.~orig)
}

// predicate

pred showMove {
  some v1, v2, v3 : Vehicle | not (v1.pos = v2.pos or v1.pos = v3.pos or v2.pos = v3.pos)
                                            and
                                            after after after after after (v1.pos in Intersection and v1.pos = v2.pos and v1.pos = v3.pos)
                                            and
                                            not (v1.pos = v1.pos' or v1.pos' = v1.pos'' or v1.pos'' = v1.pos''')
}

// command

run showMove for 8 but 10 NetworkElement








//////////////////   STEP 3  /////////////////////////////


// Facts
fact noCarsLeaveAccident {
  always all i : Intersection | i.hasAccident = true implies i.~pos = i.~pos'
}

/*
// This predicate and command have been introduced only for validating the model,
// they are not part of the solution to be uploaded.
pred showAccident {
  some i : Intersection | eventually (not i.~pos = none and i.hasAccident = true ; i.hasAccident = true ; i.hasAccident = true)
  and
  some i : Intersection | always (not i.~pos =i.~pos')
}

run showAccident for 5 but 10 NetworkElement
*/

// assertion 

assert trafficStuckInAccident {
  always all i : Intersection, v : Vehicle | i.hasAccident = true and v.pos in Road and v.pos.dest = i
                                                              implies
                                                              v.pos = v.pos'
}


// command

check trafficStuckInAccident for 8 but 10 NetworkElement
