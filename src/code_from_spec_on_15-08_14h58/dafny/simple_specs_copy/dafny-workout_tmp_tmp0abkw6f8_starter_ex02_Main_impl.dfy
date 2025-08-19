//ATOM
method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
  /* code modified by LLM (iteration 1): Fixed implementation to satisfy postconditions without assume statements */
  y := -x;
}

//IMPL 
method Main()
{
	var a := Abs(-3);
}