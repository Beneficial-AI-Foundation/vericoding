//IMPL 
method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
	c := if a >= b then a else b;
}