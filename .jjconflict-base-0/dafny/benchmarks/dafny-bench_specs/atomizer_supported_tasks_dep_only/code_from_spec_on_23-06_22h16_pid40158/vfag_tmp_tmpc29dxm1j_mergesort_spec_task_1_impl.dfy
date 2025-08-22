//IMPL ordenar_mergesort
method ordenar_mergesort(V : array?<int>)
    requires V != null
    modifies V
{
    if V.Length > 0 {
        mergesort(V, 0, V.Length);
    }
}

//IMPL mergesort
method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires c >= 0 && f <= V.Length
    modifies V
    decreases f - c
{
    if c < f - 1 {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m, f);
        mezclar(V, c, m, f);
    }
}

//IMPL mezclar
method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length
    modifies V
{
    if c >= f {
        return;
    }
    
    var left := new int[m - c];
    var right := new int[f - m];
    
    // Copy data to temporary arrays
    var i := 0;
    while i < m - c
        invariant 0 <= i <= m - c
        invariant left.Length == m - c
        invariant c + i <= V.Length
        decreases m - c - i
    {
        left[i] := V[c + i];
        i := i + 1;
    }
    
    i := 0;
    while i < f - m
        invariant 0 <= i <= f - m
        invariant right.Length == f - m
        invariant m + i <= V.Length
        decreases f - m - i
    {
        right[i] := V[m + i];
        i := i + 1;
    }
    
    // Merge the temporary arrays back into V[c..f]
    var i1 := 0;
    var i2 := 0;
    var k := c;
    
    while i1 < left.Length && i2 < right.Length
        invariant 0 <= i1 <= left.Length
        invariant 0 <= i2 <= right.Length
        invariant c <= k <= f
        invariant k == c + i1 + i2
        /* code modified by LLM (iteration 2): weakened bounds check to allow k to reach f */
        invariant k <= V.Length
        decreases (left.Length - i1) + (right.Length - i2)
    {
        if left[i1] <= right[i2] {
            V[k] := left[i1];
            i1 := i1 + 1;
        } else {
            V[k] := right[i2];
            i2 := i2 + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements of left[], if any
    while i1 < left.Length
        invariant 0 <= i1 <= left.Length
        invariant c <= k <= f
        invariant k == c + i1 + i2
        /* code modified by LLM (iteration 2): weakened bounds check to allow k to reach f */
        invariant k <= V.Length
        decreases left.Length - i1
    {
        V[k] := left[i1];
        i1 := i1 + 1;
        k := k + 1;
    }
    
    // Copy remaining elements of right[], if any
    while i2 < right.Length
        invariant 0 <= i2 <= right.Length
        invariant c <= k <= f
        invariant k == c + i1 + i2
        /* code modified by LLM (iteration 2): weakened bounds check to allow k to reach f */
        invariant k <= V.Length
        decreases right.Length - i2
    {
        V[k] := right[i2];
        i2 := i2 + 1;
        k := k + 1;
    }
}