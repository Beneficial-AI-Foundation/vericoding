//ATOM

predicate sorted_seq(a: seq<int>)
{
 forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}


//ATOM

predicate sorted_slice(a: array<int>, start: int, end: int)
 requires 0 <= start <= end <= a.Length
 reads a
{
 forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}


//IMPL mergeSimple
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
 modifies b
 requires sorted_seq(a1)
 requires sorted_seq(a2)
 requires 0 <= start <= end <= b.Length
 requires |a1| + |a2| == end - start
 ensures sorted_slice(b, start, end)
{
    var i1 := 0;
    var i2 := 0;
    var pos := start;
    
    /* code modified by LLM (iteration 4): Simplified invariants focusing on essential properties */
    while i1 < |a1| && i2 < |a2| && pos < end
        invariant 0 <= i1 <= |a1|
        invariant 0 <= i2 <= |a2|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i1 < |a1| && pos > start ==> b[pos-1] <= a1[i1]
        invariant i2 < |a2| && pos > start ==> b[pos-1] <= a2[i2]
    {
        if a1[i1] <= a2[i2] {
            b[pos] := a1[i1];
            i1 := i1 + 1;
        } else {
            b[pos] := a2[i2];
            i2 := i2 + 1;
        }
        pos := pos + 1;
    }
    
    /* code modified by LLM (iteration 4): Simplified invariants for remaining a1 elements */
    while i1 < |a1| && pos < end
        invariant 0 <= i1 <= |a1|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i1 < |a1| && pos > start ==> b[pos-1] <= a1[i1]
        invariant i2 == |a2|
    {
        b[pos] := a1[i1];
        i1 := i1 + 1;
        pos := pos + 1;
    }
    
    /* code modified by LLM (iteration 4): Simplified invariants for remaining a2 elements */
    while i2 < |a2| && pos < end
        invariant 0 <= i2 <= |a2|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i2 < |a2| && pos > start ==> b[pos-1] <= a2[i2]
        invariant i1 == |a1|
    {
        b[pos] := a2[i2];
        i2 := i2 + 1;
        pos := pos + 1;
    }
}