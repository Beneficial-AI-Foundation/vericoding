

// <vc-helpers>
lemma largestEven_ge_any_even(x:int,y:int)
  requires 0 <= x && 0 <= y && x < y
  ensures (if y % 2 == 0 then y else y - 1) % 2 == 0
  ensures (if y % 2 == 0 then y else y - 1) <= y
  ensures forall i :: x <= i <= y && i % 2 == 0 ==> (if y % 2 == 0 then y else y - 1) >= i
{
  if y % 2 == 0 {
    var r := y;
    assert r % 2 == 0;
    assert r <= y;
    assert forall i :: x <= i <= y && i % 2 == 0 ==> r >= i;
  } else {
    var r := y - 1;
    assert y % 2 != 0;
    assert r % 2 == 0;
    assert r <= y;
    assert forall i :: x <= i <= y && i % 2 == 0 ==> r >= i;
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
    num := -1;
    return;
  }
  if y % 2 == 0 {
    num := y;
  } else {
    num := y - 1;
  }
  largestEven_ge_any_even(x, y);
  assert num == (if y % 2 == 0 then y else y - 1);
  return;
}
// </vc-code>

