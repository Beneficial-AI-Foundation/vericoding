

// <vc-helpers>
lemma ForallOrNotForall(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  ensures (forall i :: 0 <= i < |a| ==> a[i] > b[i]) || 
          (exists i :: 0 <= i < |a| && a[i] <= b[i])
{
  if exists i :: 0 <= i < |a| && a[i] <= b[i] {
  } else {
    // Show that forall holds
  }
}
// </vc-helpers>

// <vc-spec>
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
// </vc-spec>
// <vc-code>
{
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant forall i :: 0 <= i < j ==> a[i] > b[i]
  {
    if a[j] <= b[j] {
      return false;
    }
    j := j + 1;
  }
  return true;
}
// </vc-code>

