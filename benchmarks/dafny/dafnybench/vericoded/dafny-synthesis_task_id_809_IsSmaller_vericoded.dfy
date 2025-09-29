

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
  result := true;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant result <==> forall i :: 0 <= i < j ==> a[i] > b[i]
    invariant !result <==> exists i :: 0 <= i < j && a[i] <= b[i]
  {
    if a[j] <= b[j] {
      result := false;
      break;
    }
    j := j + 1;
  }
}
// </vc-code>

