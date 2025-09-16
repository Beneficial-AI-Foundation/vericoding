// <vc-preamble>
// ======= TASK =======
// Implement a function that takes two integers as input and returns their sum.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(x: int, y: int)
{
    true
}

function CorrectSum(x: int, y: int): int
{
    x + y
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method add(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures result == CorrectSum(x, y)
// </vc-spec>
// <vc-code>
{
    result := x + y;
}
// </vc-code>
