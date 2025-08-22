//IMPL 
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
  /* code modified by LLM (iteration 3): Simplified brute force approach with correct invariants */
  var minDiff := if a[0] < b[0] then (b[0] - a[0]) else (a[0] - b[0]);
  var bestI := 0;
  var bestJ := 0;
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= bestI < a.Length && 0 <= bestJ < b.Length
    invariant minDiff == if a[bestI] < b[bestJ] then (b[bestJ] - a[bestI]) else (a[bestI] - b[bestJ])
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> minDiff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= bestI < a.Length && 0 <= bestJ < b.Length
      invariant minDiff == if a[bestI] < b[bestJ] then (b[bestJ] - a[bestI]) else (a[bestI] - b[bestJ])
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> minDiff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
      invariant forall jj :: 0 <= jj < j ==> minDiff <= if a[i] < b[jj] then (b[jj] - a[i]) else (a[i] - b[jj])
    {
      var currentDiff := if a[i] < b[j] then (b[j] - a[i]) else (a[i] - b[j]);
      
      if currentDiff < minDiff {
        /* code modified by LLM (iteration 3): Update best pair when better difference found */
        minDiff := currentDiff;
        bestI := i;
        bestJ := j;
      }
      
      j := j + 1;
    }
    i := i + 1;
  }
  
  d := minDiff;
}