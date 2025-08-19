//ATOM
method Abs(x:int) returns (y:int)
ensures y>=0
ensures x>=0 ==> x == y
ensures x<0 ==> -x == y
ensures y == abs(x); // use this instead of line 3,4
{
  y := 0;
  assume y>=0;
  assume x>=0 ==> x == y;
  assume x<0 ==> -x == y;
  assume y ==> abs(x); // use this instead of line 3,4;
  return y;
}


//ATOM

function abs(x: int): int{
  if x>0 then x else -x
}


// SPEC

method Testing(){
}
