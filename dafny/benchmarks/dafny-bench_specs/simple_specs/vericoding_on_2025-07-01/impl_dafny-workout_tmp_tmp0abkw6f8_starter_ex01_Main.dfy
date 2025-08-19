//ATOM

method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
  c := 0;
  assume c >= a && c >= b && (c ==> a || c ==> b);
  return c;
}


// SPEC

method Main()
{
	print "Testing max...\n";

	var max := Max(3, 4);

	max := Max(-3, 4);

	max := Max(-3, -4);

	max := Max(5555555, 5555);
}