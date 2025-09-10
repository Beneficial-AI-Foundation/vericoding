function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
// (No helper lemmas required)
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
  var m := min(a);

  // find an index of the minimal element m
  var idxMin := 0;
  while idxMin < |a|
    invariant 0 <= idxMin <= |a|
    invariant forall t :: 0 <= t < idxMin ==> a[t] != m
  {
    if a[idxMin] == m {
      break;
    }
    idxMin := idxMin + 1;
  }
  // prove that we indeed found such an index (uses min(a) in a)
  assert idxMin < |a__| by {
    // rename to avoid clash inside proof (Dafny sometimes needs unique names in
// </vc-code>

