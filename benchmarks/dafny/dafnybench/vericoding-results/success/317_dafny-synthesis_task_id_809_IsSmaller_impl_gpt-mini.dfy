

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[k] > b[k]
    decreases n - i
  {
    if a[i] <= b[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

