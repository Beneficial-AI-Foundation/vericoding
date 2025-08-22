//IMPL find_min_index
method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
    min_i := s;
    var i := s + 1;
    
    /* code modified by LLM (iteration 4): Removed problematic invariant min_i < i and adjusted bounds */
    while i < e
        invariant s <= min_i < e
        invariant s + 1 <= i <= e
        invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] < a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }
}

//ATOM is_sorted
predicate is_sorted(a: seq<int>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

//ATOM is_permutation
predicate is_permutation(a:seq<int>, b:seq<int>)
decreases |a|
decreases |b|
{
    |a| == |b|  && ((|a| == 0 && |b| == 0) ||  exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
}

//ATOM is_permutation2
predicate is_permutation2(a: array<int>, b: array<int>)
reads a, b
{
    is_permutation(a[..], b[..])
}

//ATOM selection_sort
method selection_sort(a: array<int>)
modifies a
ensures is_sorted(a[..])
ensures is_permutation2(a, old(a))
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length
        invariant forall x, y :: 0 <= x < i && i <= y < a.Length ==> a[x] <= a[y]
        invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
        invariant is_permutation2(a, old(a))
    {
        var min_idx := find_min_index(a, i, a.Length);
        
        var temp := a[i];
        a[i] := a[min_idx];
        a[min_idx] := temp;
        
        i := i + 1;
    }
}