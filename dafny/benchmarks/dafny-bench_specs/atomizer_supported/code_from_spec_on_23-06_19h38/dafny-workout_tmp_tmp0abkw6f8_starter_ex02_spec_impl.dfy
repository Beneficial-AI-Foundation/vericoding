//IMPL 
method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
	y := -x;
}

//IMPL 
method Main()
{
}