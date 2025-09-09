This verification task implements a simple addition function that takes two integers as input and returns their sum. The implementation should correctly add the two input integers and satisfy the postcondition that the result equals the mathematical sum of the inputs.

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

// ======= HELPERS =======

// ======= MAIN METHOD =======
method add(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures result == CorrectSum(x, y)
{
    result := x + y;
}
