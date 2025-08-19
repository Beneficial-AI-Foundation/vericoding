//ATOM
method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
  /* code modified by LLM (iteration 1): Fixed syntax error and implemented proper max logic */
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

//IMPL 
method Main()
{
	/* code modified by LLM (iteration 2): Ensured proper variable handling and method calls */
	print "Testing max...\n";

	var max := Max(3, 4);
	print "Max(3, 4) = ", max, "\n";

	max := Max(-3, 4);
	print "Max(-3, 4) = ", max, "\n";

	max := Max(-3, -4);
	print "Max(-3, -4) = ", max, "\n";

	max := Max(5555555, 5555);
	print "Max(5555555, 5555) = ", max, "\n";
}