//IMPL fillK
method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
{
    var count := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant count == |set j | 0 <= j < i && a[j] == k|
    {
        if a[i] == k {
            count := count + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 2): added missing return statement */
    b := count >= c;
    return;
}

/* code modified by LLM (iteration 2): added helper predicate for substring matching */
predicate isMatchAt(a: array<char>, b: array<char>, pos: int)
    reads a, b
    requires 0 <= pos <= a.Length
{
    pos + b.Length <= a.Length && 
    forall j :: 0 <= j < b.Length ==> a[pos + j] == b[j]
}

//IMPL containsSubString
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
{
    if b.Length == 0 {
        pos := 0;
        return;
    }
    
    var i := 0;
    while i <= a.Length - b.Length
        invariant 0 <= i <= a.Length - b.Length + 1
        /* code modified by LLM (iteration 2): fixed invariant to properly express no match found before position i */
        invariant forall k :: 0 <= k < i ==> !isMatchAt(a, b, k)
    {
        var j := 0;
        /* code modified by LLM (iteration 2): simplified matching logic by checking character by character */
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant forall k :: 0 <= k < j ==> a[i + k] == b[k]
        {
            if a[i + j] != b[j] {
                break;
            }
            j := j + 1;
        }
        
        if j == b.Length {
            /* code modified by LLM (iteration 2): added assertion to help verification */
            assert forall k :: 0 <= k < b.Length ==> a[i + k] == b[k];
            assert isMatchAt(a, b, i);
            pos := i;
            return;
        }
        
        i := i + 1;
    }
    
    pos := -1;
}