//IMPL
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
	/* code modified by LLM (iteration 1): explicit assignment with clear logic */
	y := -x;
	/* code modified by LLM (iteration 1): assertion to help verification */
	assert x == -1;
	assert y == 1;
	assert 0 <= y;
	assert x < 0 ==> y == -x;
}