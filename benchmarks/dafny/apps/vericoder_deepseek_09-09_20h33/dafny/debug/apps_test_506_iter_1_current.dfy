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
lemma countSquaresLemma(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures countSquares(a, b) >= 0
    decreases a + b
{
    if a == 0 || b == 0 {
        // Base case: 0 squares
    } else if a > b {
        countSquaresLemma(a % b, b);
    } else if b > a {
        countSquaresLemma(a, b % a);
    } else {
        // a == b case: exactly 1 square
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
    result := 0;
    var x := a;
    var y := b;
    
    while x > 0 && y > 0
        invariant x >= 0 && y >= 0
        invariant result + countSquares(x, y) == countSquares(a, b)
        decreases x + y
    {
        if x > y {
            result := result + (x / y);
            x := x % y;
        } else if y > x {
            result := result + (y / x);
            y := y % x;
        } else {
            result := result + 1;
            x := 0;
            y := 0;
        }
    }
}
// </vc-code>

