//IMPL square
method square (n: int) returns (r: int)
	requires 0 <= n;
	ensures r == n*n;
{
	r := n * n;
}