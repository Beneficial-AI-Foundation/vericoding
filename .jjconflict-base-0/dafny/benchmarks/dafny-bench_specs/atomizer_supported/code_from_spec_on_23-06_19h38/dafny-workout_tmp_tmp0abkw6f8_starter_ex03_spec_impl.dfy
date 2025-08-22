//IMPL 
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
	if x < 0 {
		y := -x;
	} else {
		y := x;
	}
}


//IMPL 
method Abs2(x: real) returns (y: real)
	requires x == -0.5
	ensures 0.0 <= y
	ensures 0.0 <= x ==> y == x
	ensures x < 0.0 ==> y == -x
{
	if x < 0.0 {
		y := -x;
	} else {
		y := x;
	}
}


//IMPL 
method Main()
{
}