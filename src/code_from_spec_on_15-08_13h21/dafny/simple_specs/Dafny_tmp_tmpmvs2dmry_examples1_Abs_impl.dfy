//ATOM

function abs(x: int): int{
  if x>0 then x else -x
}


//IMPL 
method Abs(x:int) returns (y:int)
ensures y>=0
ensures x>=0 ==> x == y
ensures x<0 ==> -x == y
/* code modified by LLM (iteration 1): removed unnecessary semicolon after ensures clause */
ensures y == abs(x) // use this instead of line 3,4
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}