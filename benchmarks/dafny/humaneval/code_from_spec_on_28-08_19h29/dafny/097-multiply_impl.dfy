function last_digit(n: int): int
  // post-conditions-start
  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10
  // post-conditions-end
{
  // impl-start
  if n < 0 then (-n) % 10 else n % 10
  // impl-end
}

// <vc-helpers>
function get_last_digit(n: int): int
  ensures n >= 0 ==> get_last_digit(n) == n % 10
  ensures n < 0 ==> get_last_digit(n) == (-n) % 10
{
  if n < 0 then (-n) % 10 else n % 10
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def multiply(a : Int, b : Int) -> Int
Complete the function that takes two integers and returns the product of their unit digits. Assume the input is always valid.
*/
// </vc-description>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
  ensures result == get_last_digit(a) * get_last_digit(b)
// </vc-spec>
// <vc-code>
{
  var digit_a := get_last_digit(a);
  var digit_b := get_last_digit(b);
  result := digit_a * digit_b;
}
// </vc-code>
