

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
  var i := 0;
  var found := false;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant found ==> (exists j :: 0 <= j < i && a[j] <= b[j])
    invariant !found ==> (forall j :: 0 <= j < i ==> a[j] > b[j])
    decreases |a| - i
  {
    if a[i] <= b[i] {
      found := true;
    }
    i := i + 1;
  }
  result := !found;
}
// </vc-code>

