predicate ValidInput(a: int, b: int)
{
    a > 0 && b > 0
}

function countSquares(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures a > 0 && b > 0 && a > b ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && b > a ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && a == b ==> countSquares(a, b) == 1
    decreases a + b
{
    if a == 0 || b == 0 then 0
    else if a > b then a / b + countSquares(a % b, b)
    else b / a + countSquares(a, b % a)
}

// <vc-helpers>
lemma CountSquaresAtLeastZero(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures countSquares(a, b) >= 0
    decreases a + b
{
    if a == 0 || b == 0 {
        assert countSquares(a, b) == 0;
        assert 0 >= 0;
    } else if a > b {
        CountSquaresAtLeastZero(a % b, b);
        assert a / b + countSquares(a % b, b) >= 0;
    } else if b > a {
        CountSquaresAtLeastZero(a, b % a);
        assert b / a + countSquares(a, b % a) >= 0;
    } else {
        assert countSquares(a, b) == 1;
        assert 1 >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures (a == b) ==> (result == 1)
    ensures a > b ==> result >= 1
    ensures result == countSquares(a, b)
// </vc-spec>
// <vc-code>
{ 
  result := countSquares(a, b); 
  CountSquaresAtLeastZero(a, b); 
  assert result >= 0;
}
// </vc-code>

