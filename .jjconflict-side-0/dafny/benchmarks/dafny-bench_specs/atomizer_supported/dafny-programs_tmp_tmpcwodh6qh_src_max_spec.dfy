// SPEC 
method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
}

 
// SPEC 
 
method MaxTest() {
}


// ATOM 

function max(a: int, b: int): int
{
  if a > b then a else b
}


// SPEC 

method maxTest() {
}


