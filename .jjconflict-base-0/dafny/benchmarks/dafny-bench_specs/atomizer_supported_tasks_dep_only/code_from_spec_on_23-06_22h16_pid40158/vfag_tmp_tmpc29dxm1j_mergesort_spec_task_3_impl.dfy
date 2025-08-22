//ATOM_PLACEHOLDER_ordenar_mergesort



//ATOM_PLACEHOLDER_mergesort



//IMPL mezclar
method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length
    modifies V
{
    if c == f {
        return;
    }
    
    // Create temporary arrays to hold the two subarrays
    var left := new int[m - c];
    var right := new int[f - m];
    
    // Copy data to temporary arrays
    var i := 0;
    while i < m - c
        invariant 0 <= i <= m - c
    {
        left[i] := V[c + i];
        i := i + 1;
    }
    
    var j := 0;
    while j < f - m
        invariant 0 <= j <= f - m
    {
        right[j] := V[m + j];
        j := j + 1;
    }
    
    // Merge the temporary arrays back into V[c..f]
    i := 0;
    j := 0;
    var k := c;
    
    while i < m - c && j < f - m
        invariant 0 <= i <= m - c
        invariant 0 <= j <= f - m
        invariant c <= k <= f
        invariant k == c + i + j
    {
        if left[i] <= right[j] {
            V[k] := left[i];
            i := i + 1;
        } else {
            V[k] := right[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements of left[], if any
    while i < m - c
        invariant 0 <= i <= m - c
        invariant c <= k <= f
        invariant k == c + i + j
    {
        V[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements of right[], if any
    while j < f - m
        invariant 0 <= j <= f - m
        invariant c <= k <= f
        invariant k == c + i + j
    {
        V[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
}