sig Number{}

sig RowId{}{ #RowId = 3 }


sig Ticket{
  numbers : RowId -> some Number
}{
  //There are exactly 3 different rows
  #(numbers.Number) = 3

  //There are exactly 5 different numbers per row
  all r : RowId | #(numbers[r]) = 5

  //All numbers in a ticket are different
  #(RowId.numbers) = 15
}

sig Coordinator{
  tickets : some Ticket,
  drawn : set Number
}


pred win5InARow[c: Coordinator, t: Ticket] {
  some r: RowId | 
    t in c.tickets and r in t.(numbers.Number) and
    t.numbers[r] in c.drawn
}

pred bingo[c: Coordinator, t: Ticket] {
  t in c.tickets and
  all r: RowId | r in t.(numbers.Number) and t.numbers[r] in c.drawn
}

pred draw [g, g' : Coordinator, num : Number]{
  //precondition
  not num in g.drawn
  //postcondition
  g'.tickets = g.tickets
  g'.drawn = g.drawn + num
}

pred show{ 
  #Ticket = 1
  #Coordinator = 1
  #Coordinator.drawn < 15
}

run show for 20 but 1 Coordinator, 2 Ticket

run draw for 20 but 2 Coordinator, 3 Ticket

run win5InARow for 20 but 2 Coordinator, 3 Ticket

run bingo for 20 but 2 Coordinator, 3 Ticket
