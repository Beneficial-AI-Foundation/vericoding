// IMPL ordenar_mergesort
method ordenar_mergesort(V : array?<int>)
    requires V != null
    modifies V
{
    if V.Length > 1 {
        mergesort(V, 0, V.Length);
    }
}

// IMPL mergesort
method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires c >= 0 && f <= V.Length
    modifies V
    /* code modified by LLM (iteration 1): Added decreases clause for termination */
    decreases f - c
{
    if f - c > 1 {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m, f);
        mezclar(V, c, m, f);
    }
}

// IMPL mezclar
method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length
    modifies V
{
    if c < m && m < f {
        var temp := new int[f - c];
        var i := c;
        var j := m;
        var k := 0;
        
        /* code modified by LLM (iteration 1): Fixed loop condition and added proper decreases clause */
        while i < m || j < f
            invariant 0 <= k <= temp.Length
            invariant c <= i <= m
            invariant m <= j <= f
            invariant k == (i - c) + (j - m)
            invariant temp.Length == f - c
            decreases (m - i) + (f - j)
        {
            /* code modified by LLM (iteration 1): Corrected merge logic with proper boundary checks */
            if i < m && (j >= f || V[i] <= V[j]) {
                temp[k] := V[i];
                i := i + 1;
            } else if j < f {
                temp[k] := V[j];
                j := j + 1;
            }
            k := k + 1;
        }
        
        /* code modified by LLM (iteration 1): Copy back with proper invariants */
        k := 0;
        while k < temp.Length
            invariant 0 <= k <= temp.Length
            invariant temp.Length == f - c
            decreases temp.Length - k
        {
            V[c + k] := temp[k];
            k := k + 1;
        }
    }
}