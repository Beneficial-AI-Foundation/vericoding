//ATOM
method Abs(x:int) returns (y:int)
ensures y>=0
ensures x>=0 ==> x == y
ensures x<0 ==> -x == y
/* code modified by LLM (iteration 1): removed semicolon after ensures clause */
ensures y == abs(x) // use this instead of line 3,4
{
  /* code modified by LLM (iteration 1): replaced assume statements with proper implementation */
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

//ATOM
function abs(x: int): int{
  if x>0 then x else -x
}

//IMPL Testing
method Testing(){
}