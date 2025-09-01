

// <vc-helpers>
lemma largest_even_helper(x: int, y: int, num: int)
  requires 0 <= x && 0 <= y
  requires x < y
  requires (y % 2 == 0 && num == y) || (y % 2 != 0 && num == y-1)
  ensures forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i
{
  if y % 2 == 0 {
    forall i : int | x <= i <= y && i % 2 == 0
      ensures num >= i
    {
    }
  } else {
    forall i : int | x <= i <= y && i % 2 == 0
      ensures num >= i
    {
      assert i != y;
      assert i <= y-1;
    }
  }
}
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
  if y % 2 == 0 {
    num := y;
  } else {
    num := y - 1;
  }
  largest_even_helper(x, y, num);
  return num;
}
// </vc-code>

