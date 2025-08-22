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
    var k := start;
    
    /* code modified by LLM (iteration 4): comprehensive invariants with cross-sequence ordering */
    while i1 < |a1| && i2 < |a2| && k < end
        invariant 0 <= i1 <= |a1|
        invariant 0 <= i2 <= |a2|
        invariant start <= k <= end
        invariant i1 + i2 == k - start
        invariant sorted_slice(b, start, k)
        invariant i1 < |a1| && k > start ==> b[k-1] <= a1[i1]
        invariant i2 < |a2| && k > start ==> b[k-1] <= a2[i2]
        invariant forall idx :: 0 <= idx < i1 ==> (k > start ==> a1[idx] <= b[k-1])
        invariant forall idx :: 0 <= idx < i2 ==> (k > start ==> a2[idx] <= b[k-1])
        invariant forall idx :: i1 <= idx < |a1| ==> (k > start ==> b[k-1] <= a1[idx])
        invariant forall idx :: i2 <= idx < |a2| ==> (k > start ==> b[k-1] <= a2[idx])
    {
        if a1[i1] <= a2[i2] {
            b[k] := a1[i1];
            i1 := i1 + 1;
        } else {
            b[k] := a2[i2];
            i2 := i2 + 1;
        }
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): strengthened invariants for a1 remainder with cross-sequence bounds */
    while i1 < |a1| && k < end
        invariant 0 <= i1 <= |a1|
        invariant i2 == |a2|
        invariant start <= k <= end
        invariant i1 + i2 == k - start
        invariant sorted_slice(b, start, k)
        invariant i1 < |a1| && k > start ==> b[k-1] <= a1[i1]
        invariant forall idx :: 0 <= idx < i2 ==> (k > start ==> a2[idx] <= b[k-1])
        invariant forall idx :: i1 <= idx < |a1| ==> (k > start ==> b[k-1] <= a1[idx])
    {
        b[k] := a1[i1];
        i1 := i1 + 1;
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): strengthened invariants for a2 remainder with cross-sequence bounds */
    while i2 < |a2| && k < end
        invariant i1 == |a1|
        invariant 0 <= i2 <= |a2|
        invariant start <= k <= end
        invariant i1 + i2 == k - start
        invariant sorted_slice(b, start, k)
        invariant i2 < |a2| && k > start ==> b[k-1] <= a2[i2]
        invariant forall idx :: 0 <= idx < i1 ==> (k > start ==> a1[idx] <= b[k-1])
        invariant forall idx :: i2 <= idx < |a2| ==> (k > start ==> b[k-1] <= a2[idx])
    {
        b[k] := a2[i2];
        i2 := i2 + 1;
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to establish postcondition */
    assert k == end;
    assert i1 == |a1| && i2 == |a2|;
}