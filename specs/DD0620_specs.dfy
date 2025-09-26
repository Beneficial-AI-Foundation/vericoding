// <vc-preamble>
function abs(x: int): int
{
    if x < 0 then -x else x
}



// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
    // Fill in an expression here.
    if a > b then a else b
}


// Exercise 6:
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (y: int)
    ensures abs(x) == y
// </vc-spec>
// <vc-code>
{
    // Then change this body to also use abs.
    if x < 0 {
        return -x;
    } else {
        return x;
    }
}
// </vc-code>

// Ghost
ghost function Double(val:int) : int
{
    2 * val
}