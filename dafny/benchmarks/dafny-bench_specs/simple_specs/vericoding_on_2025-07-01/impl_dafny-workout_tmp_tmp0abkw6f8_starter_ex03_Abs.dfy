- `requires x == -1`: The input is constrained to be exactly -1
- `ensures 0 <= y`: The result must be non-negative
- `ensures 0 <= x ==> y == x`: If x is non-negative, return x unchanged
- `ensures x < 0 ==> y == -x`: If x is negative, return -x

Since the precondition requires `x == -1`, we know that `x < 0`, so the third postcondition applies: `y == -x`. With `x == -1`, we get `y == -(-1) == 1`.

//IMPL
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
	y := -x;
}