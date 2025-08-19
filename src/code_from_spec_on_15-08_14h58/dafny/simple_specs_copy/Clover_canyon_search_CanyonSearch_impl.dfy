// IMPL
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
 requires a.Length !=0 && b.Length!=0
 requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
 requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
 ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
 ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
    var i := 0;
    var j := 0;
    var minDiff := if a[0] < b[0] then b[0] - a[0] else a[0] - b[0];
    var witnessI := 0;
    var witnessJ := 0;
    
    /* code modified by LLM (iteration 3): Simplified to use nested loops for cleaner verification */
    for ii := 0 to a.Length
        invariant 0 <= witnessI < a.Length && 0 <= witnessJ < b.Length
        invariant minDiff == if a[witnessI] < b[witnessJ] then b[witnessJ] - a[witnessI] else a[witnessI] - b[witnessJ]
        invariant forall x, y :: 0 <= x < ii && 0 <= y < b.Length ==> minDiff <= if a[x] < b[y] then b[y] - a[x] else a[x] - b[y]
    {
        for jj := 0 to b.Length
            invariant 0 <= witnessI < a.Length && 0 <= witnessJ < b.Length
            invariant minDiff == if a[witnessI] < b[witnessJ] then b[witnessJ] - a[witnessI] else a[witnessI] - b[witnessJ]
            invariant forall x, y :: 0 <= x < ii && 0 <= y < b.Length ==> minDiff <= if a[x] < b[y] then b[y] - a[x] else a[x] - b[y]
            invariant forall y :: 0 <= y < jj ==> minDiff <= if a[ii] < b[y] then b[y] - a[ii] else a[ii] - b[y]
        {
            var currentDiff := if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj];
            
            if currentDiff < minDiff {
                /* code modified by LLM (iteration 3): Update minimum and witnesses */
                minDiff := currentDiff;
                witnessI := ii;
                witnessJ := jj;
            }
        }
    }
    
    d := minDiff;
}