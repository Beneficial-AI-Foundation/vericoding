

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
    num := -1;
  } else {
    if y % 2 == 0 {
      num := y;
      assert num >= x;
      assert num <= y;
      assert num >= 0;
    } else {
      num := y - 1;
      assert x < y;
      assert x <= y - 1;
      assert num >= x;
      assert num <= y;
      assert 0 < y;
      assert num >= 0;
    }
    assert num % 2 == 0;
    assert num != -1;
    forall i | x <= i <= y && i % 2 == 0
      ensures num >= i
    {
      if y % 2 == 0 {
        assert i <= y;
      } else {
        if i <= y - 1 {
        } else {
          assert i >= y;
          assert i == y;
          assert y % 2 != 0;
          assert i % 2 == 0;
          assert false;
        }
      }
    }
  }
}
// </vc-code>

