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
lemma CountSquaresTermination(a: int, b: int)
    requires a > 0 && b > 0
    ensures a > b ==> a % b < a && (a % b) + b < a + b
    ensures b > a ==> b % a < b && a + (b % a) < a + b
{
    // Dafny can prove this automatically
}

lemma CountSquaresProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures a == b ==> countSquares(a, b) == 1
    ensures a > b ==> countSquares(a, b) == a / b + countSquares(a % b, b)
    ensures b > a ==> countSquares(a, b) == b / a + countSquares(a, b % a)
{
    // Direct from the function definition
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
    var x := a;
    var y := b;
    result := 0;
    
    while x > 0 && y > 0
        invariant x >= 0 && y >= 0
        invariant result >= 0
        invariant result + countSquares(x, y) == countSquares(a, b)
        decreases x + y
    {
        if x > y {
            result := result + x / y;
            x := x % y;
        } else if y > x {
            result := result + y / x;
            y := y % x;
        } else { // x == y
            result := result + 1;
            x := 0;
            y := 0;
        }
    }
    
    assert x == 0 || y == 0;
    assert countSquares(x, y) == 0;
}
// </vc-code>

