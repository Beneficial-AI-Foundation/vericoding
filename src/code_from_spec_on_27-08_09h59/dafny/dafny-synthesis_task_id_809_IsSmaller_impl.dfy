// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  result := true;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result <==> forall j :: 0 <= j < i ==> a[j] > b[j]
  {
    if a[i] <= b[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
