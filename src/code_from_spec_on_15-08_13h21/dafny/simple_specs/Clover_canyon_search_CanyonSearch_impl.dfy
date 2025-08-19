method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
 requires a.Length !=0 && b.Length!=0
 requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
 requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
 ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
 ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
    var i := 0;
    var j := 0;
    var min_diff := if a[0] < b[0] then b[0] - a[0] else a[0] - b[0];
    var witness_i := 0;
    var witness_j := 0;
    
    /* code modified by LLM (iteration 4): Simplified invariants and added proper tracking of considered pairs */
    while i < a.Length && j < b.Length
        invariant 0 <= i <= a.Length && 0 <= j <= b.Length
        invariant 0 <= witness_i < a.Length && 0 <= witness_j < b.Length
        invariant min_diff == if a[witness_i] < b[witness_j] then b[witness_j] - a[witness_i] else a[witness_i] - b[witness_j]
        invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && ((ii < i && jj < j) || (ii < i && jj == j) || (ii == i && jj < j)) ==> min_diff <= if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj]
    {
        var diff := if a[i] < b[j] then b[j] - a[i] else a[i] - b[j];
        /* code modified by LLM (iteration 4): Added assertion to help verify invariant maintenance */
        assert min_diff <= diff;
        if diff < min_diff {
            min_diff := diff;
            witness_i := i;
            witness_j := j;
        }
        
        if a[i] < b[j] {
            i := i + 1;
        } else {
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 4): Simplified invariant for second loop */
    while i < a.Length
        invariant 0 <= i <= a.Length && j <= b.Length
        invariant 0 <= witness_i < a.Length && 0 <= witness_j < b.Length
        invariant min_diff == if a[witness_i] < b[witness_j] then b[witness_j] - a[witness_i] else a[witness_i] - b[witness_j]
        invariant j > 0 ==> forall ii :: 0 <= ii < i ==> min_diff <= if a[ii] < b[j-1] then b[j-1] - a[ii] else a[ii] - b[j-1]
        invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && (ii < i || (ii >= i && jj < j)) ==> min_diff <= if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj]
    {
        if j > 0 {
            var diff := if a[i] < b[j-1] then b[j-1] - a[i] else a[i] - b[j-1];
            /* code modified by LLM (iteration 4): Added assertion to help verify invariant maintenance */
            assert min_diff <= diff;
            if diff < min_diff {
                min_diff := diff;
                witness_i := i;
                witness_j := j-1;
            }
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Simplified invariant for third loop */
    while j < b.Length
        invariant i <= a.Length && 0 <= j <= b.Length
        invariant 0 <= witness_i < a.Length && 0 <= witness_j < b.Length
        invariant min_diff == if a[witness_i] < b[witness_j] then b[witness_j] - a[witness_i] else a[witness_i] - b[witness_j]
        invariant i > 0 ==> forall jj :: 0 <= jj < j ==> min_diff <= if a[i-1] < b[jj] then b[jj] - a[i-1] else a[i-1] - b[jj]
        invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && (jj < j || (ii < i && jj >= j)) ==> min_diff <= if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj]
    {
        if i > 0 {
            var diff := if a[i-1] < b[j] then b[j] - a[i-1] else a[i-1] - b[j];
            /* code modified by LLM (iteration 4): Added assertion to help verify invariant maintenance */
            assert min_diff <= diff;
            if diff < min_diff {
                min_diff := diff;
                witness_i := i-1;
                witness_j := j;
            }
        }
        j := j + 1;
    }
    
    d := min_diff;
}