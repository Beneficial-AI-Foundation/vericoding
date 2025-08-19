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
 requires |a1| + |a2| == end - start + 1
 ensures sorted_slice(b, start, end)
{
    var i1, i2, pos := 0, 0, start;
    
    /* code modified by LLM (iteration 3): Fixed main merge loop with proper invariants */
    while i1 < |a1| && i2 < |a2| && pos < end
        invariant 0 <= i1 <= |a1|
        invariant 0 <= i2 <= |a2|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i1 < |a1| ==> forall k :: start <= k < pos ==> b[k] <= a1[i1]
        invariant i2 < |a2| ==> forall k :: start <= k < pos ==> b[k] <= a2[i2]
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
    
    /* code modified by LLM (iteration 3): Fixed second loop with proper transition invariant */
    while i1 < |a1| && pos < end
        invariant 0 <= i1 <= |a1|
        invariant 0 <= i2 <= |a2|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i2 == |a2|
        invariant i1 < |a1| ==> forall k :: start <= k < pos ==> b[k] <= a1[i1]
    {
        b[pos] := a1[i1];
        i1 := i1 + 1;
        pos := pos + 1;
    }
    
    /* code modified by LLM (iteration 3): Fixed third loop - removed problematic invariant and added proper ones */
    while i2 < |a2| && pos < end
        invariant 0 <= i2 <= |a2|
        invariant 0 <= i1 <= |a1|
        invariant start <= pos <= end
        invariant i1 + i2 == pos - start
        invariant sorted_slice(b, start, pos)
        invariant i1 == |a1|
        invariant forall k :: start <= k < pos ==> forall j :: i2 <= j < |a2| ==> b[k] <= a2[j]
    {
        b[pos] := a2[i2];
        i2 := i2 + 1;
        pos := pos + 1;
    }
}