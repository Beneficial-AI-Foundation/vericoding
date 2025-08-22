//IMPL Abs
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
	/* code modified by LLM (iteration 1): removed duplicate method definition */
	y := -x;
}

//ATOM Main