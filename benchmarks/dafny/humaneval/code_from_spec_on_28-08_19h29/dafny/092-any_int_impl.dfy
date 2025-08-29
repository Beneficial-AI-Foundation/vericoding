// <vc-helpers>
// Helper function to check if a real number is an integer
function IsInteger(x: real): bool
{
  x.Floor as real == x
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def any_int(a: float, b: float, c: float) -> bool
Create a function that takes 3 numbers. Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers. Returns false in any other cases.
*/
// </vc-description>

// <vc-spec>
method AnyInt(a: real, b: real, c: real) returns (result: bool)
  ensures result == (
    (IsInteger(a) && IsInteger(b) && IsInteger(c)) &&
    (a == b + c || b == a + c || c == a + b)
  )
// </vc-spec>
// <vc-code>
{
  if IsInteger(a) && IsInteger(b) && IsInteger(c) {
    if a == b + c || b == a + c || c == a + b {
      return true;
    }
  }
  return false;
}
// </vc-code>
