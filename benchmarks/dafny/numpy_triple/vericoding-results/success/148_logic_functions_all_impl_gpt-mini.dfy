// <vc-preamble>
// Test whether all elements in a sequence are non-zero
// </vc-preamble>

// <vc-helpers>
predicate AllNonZero(a: seq<real>) { forall i :: 0 <= i < |a| ==> a[i] != 0.0 }
// </vc-helpers>

// <vc-spec>
method All(a: seq<real>) returns (result: bool)
    // The result is true if and only if all elements are non-zero
    ensures result == (forall i :: 0 <= i < |a| ==> a[i] != 0.0)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result == (forall j :: 0 <= j < i ==> a[j] != 0.0)
    decreases |a| - i
  {
    if a[i] == 0.0 {
      result := false;
      i := |a|;
    } else {
      i := i + 1;
    }
  }
}
// </vc-code>
