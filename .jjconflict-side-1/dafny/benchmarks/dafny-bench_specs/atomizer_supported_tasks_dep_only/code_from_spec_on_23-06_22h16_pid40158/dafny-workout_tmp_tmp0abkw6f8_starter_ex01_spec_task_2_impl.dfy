//IMPL Max
method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
	if a >= b {
		c := a;
	} else {
		c := b;
	}
}

//IMPL Main
method Main()
{
}