//ATOM
method Abs(x:int) returns (y:int)
ensures y>=0
ensures x>=0 ==> x == y
ensures x<0 ==> -x == y
ensures y == abs(x); // use this instead of line 3,4
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly compute absolute value */
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

//ATOM
function abs(x: int): int{
  /* code modified by LLM (iteration 1): Fixed condition to include zero in non-negative case */
  if x >= 0 then x else -x
}

//IMPL Testing
method Testing(){
}