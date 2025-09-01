

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method choose_num(x : int, y : int) returns (num : int)
  // pre-conditions-start
  requires 0 <= x && 0 <= y
  // pre-conditions-end
  // post-conditions-start
  ensures num == -1 || (num >= x && num <= y)
  ensures num == -1 || num % 2 == 0
  ensures num == -1 || (forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i)
  ensures num == -1 <==> x >= y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if x >= y {
    return -1;
  }
  return y - (y % 2);
}
// </vc-code>

