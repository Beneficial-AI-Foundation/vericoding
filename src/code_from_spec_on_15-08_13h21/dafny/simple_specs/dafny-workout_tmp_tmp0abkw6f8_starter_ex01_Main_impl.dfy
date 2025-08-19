method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly return the maximum value */
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

//IMPL 
method Main()
{
	print "Testing max...\n";

	var max := Max(3, 4);

	max := Max(-3, 4);

	max := Max(-3, -4);

	max := Max(5555555, 5555);
}