

// <vc-helpers>
function abs(x: int): int {
  if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
// </vc-spec>
// <vc-code>
{
  var minDiff := abs(a[0] - b[0]);
  var i := 0;
  var j := 0;
  while i < a.Length && j < b.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant forall k, l :: 0 <= k < i && 0 <= l < b.Length ==> minDiff <= abs(a[k] - b[l])
    invariant forall k, l :: 0 <= k < a.Length && 0 <= l < j ==> minDiff <= abs(a[k] - b[l])
    invariant exists k, l :: 0 <= k < a.Length && 0 <= l < b.Length && abs(a[k] - b[l]) == minDiff
  {
    var currentDiff := abs(a[i] - b[j]);
    if currentDiff < minDiff {
      minDiff := currentDiff;
    }

    if a[i] < b[j] {
      i := i + 1;
    } else if b[j] < a[i] {
      j := j + 1;
    } else { // a[i] == b[j]
      minDiff := 0; 
      break;
    }
  }
  d := minDiff;
}
// </vc-code>

