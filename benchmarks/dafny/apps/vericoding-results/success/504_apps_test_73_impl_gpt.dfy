function computePosition(days: int, v0: int, v1: int, a: int, l: int): int
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    decreases days
{
    if days == 0 then 0
    else
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        afterReread + readToday
}

// <vc-helpers>
lemma ComputePositionLowerBound(days: int, v0: int, v1: int, a: int, l: int)
  requires days >= 0
  requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
  requires l < v0
  ensures computePosition(days, v0, v1, a, l) >= days
  decreases days
{
  if days == 0 {
  } else {
    ComputePositionLowerBound(days - 1, v0, v1, a, l);
    var prev := computePosition(days - 1, v0, v1, a, l);
    var afterR := if prev - l > 0 then prev - l else 0;
    var potential := v0 + a * (days - 1);
    var readToday := if v1 < potential then v1 else potential;
    assert readToday >= v0;
    if prev >= l {
      assert afterR == prev - l;
      assert afterR + readToday >= (days - 1) - l + v0;
      assert afterR + readToday >= days;
    } else {
      assert prev < l;
      assert days - 1 <= prev;
      assert days <= l;
      assert v0 >= l + 1;
      assert v0 >= days + 1;
      assert afterR == 0;
      assert afterR + readToday >= v0;
      assert afterR + readToday >= days;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(c: int, v0: int, v1: int, a: int, l: int) returns (result: int)
    requires 1 <= c <= 1000
    requires 0 <= l < v0 <= v1 <= 1000
    requires 0 <= a <= 1000
    ensures result >= 1
    ensures computePosition(result, v0, v1, a, l) >= c
    ensures forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
// </vc-spec>
// <vc-code>
{
  var days := 0;
  var pos := 0;

  while pos < c
    invariant 0 <= days
    invariant days <= c
    invariant pos == computePosition(days, v0, v1, a, l)
    invariant forall d' :: 1 <= d' && d' < days ==> computePosition(d', v0, v1, a, l) < c
    decreases c - days
  {
    var d0 := days;
    var prevPos := pos;
    assert prevPos == computePosition(d0, v0, v1, a, l);
    assert forall d' :: 1 <= d' && d' < d0 ==> computePosition(d', v0, v1, a, l) < c;

    ComputePositionLowerBound(d0, v0, v1, a, l);
    assert computePosition(d0, v0, v1, a, l) >= d0;
    assert d0 < c;

    days := days + 1;
    assert days <= c;

    pos := computePosition(days, v0, v1, a, l);

    forall d2 | 1 <= d2 && d2 < days
      ensures computePosition(d2, v0, v1, a, l) < c
    {
      if d2 < d0 {
        assert computePosition(d2, v0, v1, a, l) < c;
      } else {
        assert d2 >= d0;
        assert d2 < d0 + 1;
        assert d2 <= d0;
        assert d2 == d0;
        assert computePosition(d2, v0, v1, a, l) == prevPos;
        assert computePosition(d2, v0, v1, a, l) < c;
      }
    }
  }

  assert pos >= c;
  if days == 0 {
    assert pos == computePosition(0, v0, v1, a, l);
    assert pos == 0;
    assert pos < c;
  }

  result := days;
}
// </vc-code>

