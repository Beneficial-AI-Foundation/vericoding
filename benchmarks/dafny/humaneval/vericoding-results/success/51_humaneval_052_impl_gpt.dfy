// <vc-preamble>

predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>
predicate AllBelowPrefix(l: seq<int>, t: int, i: int)
    requires 0 <= i <= |l|
{
    forall j :: 0 <= j < i ==> l[j] < t
}
// </vc-helpers>

// <vc-spec>
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
  var ok := true;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant ok == (forall j :: 0 <= j < i ==> l[j] < t)
  {
    ok := ok && l[i] < t;
    i := i + 1;
  }
  result := ok;
}
// </vc-code>
