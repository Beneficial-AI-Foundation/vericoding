//ATOM
method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
  /* code modified by LLM (iteration 1): Fixed implementation to actually compute absolute value instead of using assumes */
  y := -x;
}

//IMPL 
method Main()
{
  /* code modified by LLM (iteration 1): Added proper variable assignment for return value */
  var a := Abs(-3);
}