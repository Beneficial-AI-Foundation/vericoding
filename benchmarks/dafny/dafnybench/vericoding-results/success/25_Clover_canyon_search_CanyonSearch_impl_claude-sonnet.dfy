

// <vc-helpers>

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
  var minDist := if a[0] < b[0] then (b[0] - a[0]) else (a[0] - b[0]);
  var bestI := 0;
  var bestJ := 0;
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= bestI < a.Length && 0 <= bestJ < b.Length
    invariant minDist == (if a[bestI] < b[bestJ] then (b[bestJ]-a[bestI]) else (a[bestI]-b[bestJ]))
    invariant forall x,y :: 0<=x<i && 0<=y<b.Length ==> minDist <= (if a[x] < b[y] then (b[y]-a[x]) else (a[x]-b[y]))
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= bestI < a.Length && 0 <= bestJ < b.Length
      invariant minDist == (if a[bestI] < b[bestJ] then (b[bestJ]-a[bestI]) else (a[bestI]-b[bestJ]))
      invariant forall x,y :: 0<=x<i && 0<=y<b.Length ==> minDist <= (if a[x] < b[y] then (b[y]-a[x]) else (a[x]-b[y]))
      invariant forall y :: 0<=y<j ==> minDist <= (if a[i] < b[y] then (b[y]-a[i]) else (a[i]-b[y]))
    {
      var currentDist := if a[i] < b[j] then (b[j] - a[i]) else (a[i] - b[j]);
      if currentDist < minDist {
        minDist := currentDist;
        bestI := i;
        bestJ := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  return minDist;
}
// </vc-code>

