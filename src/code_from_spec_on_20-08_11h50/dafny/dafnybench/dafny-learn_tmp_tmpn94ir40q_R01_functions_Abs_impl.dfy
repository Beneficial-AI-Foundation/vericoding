// <vc-spec>
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

// <vc-helpers>
// </vc-helpers>

method Abs(x: int) returns (y: int)
    ensures abs(x) == y
// </vc-spec>
// <vc-code>
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}
// </vc-code>

// Ghost
ghost function Double(val:int) : int
{
    2 * val
}