// <vc-preamble>

predicate ValidInput(x: int, y: int) {
    x > 0 && y > 0
}

predicate NoEvenInRange(x: int, y: int) {
    forall i :: x <= i <= y ==> i % 2 != 0
}

predicate IsLargestEvenInRange(x: int, y: int, result: int) {
    result % 2 == 0 && 
    x <= result <= y && 
    (forall i :: x <= i <= y && i % 2 == 0 ==> i <= result)
}

predicate CorrectResult(x: int, y: int, result: int) {
    if x > y then 
        result == -1
    else
        (result == -1 && NoEvenInRange(x, y)) ||
        IsLargestEvenInRange(x, y, result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Bound any even i under an odd upper bound y by y-1 */
lemma EvenBoundIfYOdd(i: int, y: int)
  requires i % 2 == 0
  requires i <= y
  requires y % 2 != 0
  ensures i <= y - 1
{
  assert i != y by {
    if i == y {
      assert y % 2 == 0;
      assert y % 2 != 0;
    }
  }
  assert i < y;
  assert i <= y - 1;
}

/* helper modified by LLM (iteration 3): Prove that the predecessor of a positive odd y is even */
lemma PrevEvenIfOddPositive(y: int)
  requires y > 0
  requires y % 2 != 0
  ensures (y - 1) % 2 == 0
{
  var q := y / 2;
  var r := y % 2;
  assert y == 2 * q + r;
  assert 0 <= r < 2;
  assert r != 0;
  assert r == 1;
  assert y - 1 == 2 * q + (r - 1);
  assert r - 1 == 0;
  assert y - 1 == 2 * q;
  assert (y - 1) % 2 == 0;
}

/* helper modified by LLM (iteration 3): Establish NoEvenInRange on a singleton odd range without forall-with-body */
lemma NoEvenInRangeSingleton(x: int)
  requires x % 2 != 0
  ensures NoEvenInRange(x, x)
{
  assert forall i :: x <= i <= x ==> i % 2 != 0;
}

/* helper modified by LLM (iteration 3): If y is even and within range, y is the largest even in [x,y] */
lemma LargestEvenWhenYEven(x: int, y: int)
  requires ValidInput(x, y)
  requires x <= y
  requires y % 2 == 0
  ensures IsLargestEvenInRange(x, y, y)
{
  assert y % 2 == 0;
  assert x <= y <= y;
  assert forall i :: x <= i <= y && i % 2 == 0 ==> i <= y;
}

/* helper modified by LLM (iteration 3): If y is odd and x <= y-1, then y-1 is the largest even in [x,y] */
lemma LargestEvenWhenYOdd(x: int, y: int)
  requires ValidInput(x, y)
  requires x <= y
  requires y % 2 != 0
  requires y - 1 >= x
  ensures IsLargestEvenInRange(x, y, y - 1)
{
  PrevEvenIfOddPositive(y);
  assert (y - 1) % 2 == 0;
  assert x <= y - 1 <= y;
  assert forall i :: x <= i <= y && i % 2 == 0 ==> i <= y - 1;
}
// </vc-helpers>

// <vc-spec>
method ChooseNum(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures CorrectResult(x, y, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Implement logic without forall-with-body; use lemmas */
  if x > y {
    result := -1;
  } else {
    if y % 2 == 0 {
      result := y;
      assert result == y;
      LargestEvenWhenYEven(x, y);
      assert IsLargestEvenInRange(x, y, result);
    } else {
      var e := y - 1;
      if e >= x {
        result := e;
        assert result == y - 1;
        LargestEvenWhenYOdd(x, y);
        assert IsLargestEvenInRange(x, y, result);
      } else {
        result := -1;
        assert x <= y;
        assert y - 1 < x;
        assert y <= x;
        assert x == y;
        assert y % 2 != 0;
        assert x % 2 != 0;
        NoEvenInRangeSingleton(x);
        assert x == y;
        assert NoEvenInRange(x, y);
      }
    }
  }
}
// </vc-code>
