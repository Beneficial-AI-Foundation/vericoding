// <vc-helpers>
// No additional helpers needed for this specification and implementation.
// </vc-helpers>

// <vc-description>
/*
function_signature: def choose_num(x: int, y: int) -> int
This function takes two positive numbers x and y and returns the biggest even integer number that is in the range [x, y] inclusive. If there's no such number, then the function should return -1.
*/
// </vc-description>

// <vc-spec>
method choose_num(x: int, y: int) returns (result: int)
  requires x > 0 && y > 0
  ensures result == -1 || (x <= result <= y && result % 2 == 0)
  ensures result != -1 ==> forall k :: x <= k <= y && k % 2 == 0 ==> k <= result
// </vc-spec>
// <vc-code>
{
  result := -1;
  var i := y;
  while i >= x
    invariant result == -1 || (x <= result <= y && result % 2 == 0)
    invariant result != -1 ==> forall k :: x <= k <= y && k % 2 == 0 ==> k <= result
    decreases i
  {
    if i % 2 == 0 {
      result := i;
      return;
    }
    i := i - 1;
  }
  return;
}
// </vc-code>
