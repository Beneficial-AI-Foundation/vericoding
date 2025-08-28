// <vc-helpers>
lemma MinDistanceProperties(a: array<int>, b: array<int>, i: int, j: int, min_dist: nat)
  requires a.Length > 0 && b.Length > 0
  requires forall x,y :: 0<=x<y<a.Length ==> a[x]<=a[y]
  requires forall x,y :: 0<=x<y<b.Length ==> b[x]<=b[y]
  requires 0 <= i < a.Length && 0 <= j < b.Length
  requires min_dist == if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  requires forall x,y :: 0<=x<a.Length && 0<=y<b.Length ==> min_dist <= if a[x] < b[y] then (b[y]-a[x]) else (a[x]-b[y])
  ensures exists x,y :: 0<=x<a.Length && 0<=y<b.Length && min_dist == if a[x] < b[y] then (b[y]-a[x]) else (a[x]-b[y])
  ensures forall x,y :: 0<=x<a.Length && 0<=y<b.Length ==> min_dist <= if a[x] < b[y] then (b[y]-a[x]) else (a[x]-b[y])
{
}

function AbsDiff(x: int, y: int): nat
{
  if x < y then y - x else x - y
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var min_dist := AbsDiff(a[0], b[0]);
  var best_i := 0;
  var best_j := 0;
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant exists x,y :: 0<=x<a.Length && 0<=y<b.Length && min_dist == AbsDiff(a[x], b[y])
    invariant forall x,y :: 0<=x<i && 0<=y<b.Length ==> min_dist <= AbsDiff(a[x], b[y])
    invariant 0 <= best_i < a.Length && 0 <= best_j < b.Length
    invariant min_dist == AbsDiff(a[best_i], b[best_j])
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant exists x,y :: 0<=x<a.Length && 0<=y<b.Length && min_dist == AbsDiff(a[x], b[y])
      invariant forall x,y :: 0<=x<i && 0<=y<b.Length ==> min_dist <= AbsDiff(a[x], b[y])
      invariant forall y :: 0<=y<j ==> min_dist <= AbsDiff(a[i], b[y])
      invariant 0 <= best_i < a.Length && 0 <= best_j < b.Length
      invariant min_dist == AbsDiff(a[best_i], b[best_j])
    {
      var curr_dist := AbsDiff(a[i], b[j]);
      if curr_dist < min_dist {
        min_dist := curr_dist;
        best_i := i;
        best_j := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  d := min_dist;
}
// </vc-code>
