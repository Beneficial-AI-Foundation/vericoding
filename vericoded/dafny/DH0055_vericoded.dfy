// <vc-preamble>

predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant result == (forall j :: 0 <= j < i ==> l[j] < t)
  {
    if l[i] >= t {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
