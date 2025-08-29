// <vc-helpers>
// No additional helpers needed for this fix.
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
  if x > y {
    num := -1;
  } else if x == y {
    if x % 2 == 0 {
      num := x;
    } else {
      num := -1;
    }
  } else {
    var start := if x % 2 == 0 then x else x + 1;
    if start > y {
      num := -1;
    } else {
      num := y;
      if y % 2 != 0 {
        num := y - 1;
      }
      if num < start {
        num := -1;
      }
    }
  }
}
// </vc-code>
