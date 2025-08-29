

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: def any_int(a: float, b: float, c: float) -> bool
Create a function that takes 3 numbers. Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers. Returns false in any other cases.
*/
// </vc-description>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)
  // post-conditions-start
  ensures r == (a == b + c || b == a + c || c == a + b)
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  r := (a == b + c || b == a + c || c == a + b);
}
// </vc-code>

