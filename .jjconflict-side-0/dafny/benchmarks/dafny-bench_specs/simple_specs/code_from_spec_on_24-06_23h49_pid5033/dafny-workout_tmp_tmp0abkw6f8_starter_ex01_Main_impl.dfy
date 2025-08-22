//ATOM
method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
  /* code modified by LLM (iteration 1): fixed syntax error in assume statement and provided proper implementation */
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

//IMPL Main
method Main()
{
	print "Testing max...\n";

	var max := Max(3, 4);

	max := Max(-3, 4);

	max := Max(-3, -4);

	max := Max(5555555, 5555);
}