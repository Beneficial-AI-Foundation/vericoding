//ATOM
method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
  /* code modified by LLM (iteration 1): fixed compilation errors in assume statements and implemented correct logic */
  y := -x;
}

//IMPL 
method Main()
{
	/* code modified by LLM (iteration 1): implementation remains the same as it was already correct */
	var a := Abs(-3);
}