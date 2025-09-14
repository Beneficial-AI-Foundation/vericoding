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
// No additional helpers needed for this verification
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
  var days := 1;
  while computePosition(days, v0, v1, a, l) < c
    invariant 1 <= days
    invariant forall i :: 1 <= i < days ==> computePosition(i, v0, v1, a, l) < c
    invariant days == 1 || computePosition(days - 1, v0, v1, a, l) < c
    decreases c - computePosition(days, v0, v1, a, l)
  {
    days := days + 1;
  }
  return days;
}
// </vc-code>

