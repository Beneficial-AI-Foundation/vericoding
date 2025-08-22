// IMPL find_min_index
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
    
    while (i < e)
        invariant s <= min_i < e
        invariant s <= i <= e
        invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if (a[i] < a[min_i]) {
            min_i := i;
        }
        i := i + 1;
    }
}

// ATOM 
predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

// ATOM 
predicate is_permutation(a:seq<int>, b:seq<int>)
{
    |a| == |b|  && 
    ((|a| == 0 && |b| == 0) ||  
    exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then  b[j+1..] else []))
}

// ATOM 
predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

// IMPL selection_sort
method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{
    if (ns.Length <= 1) {
        return;
    }
    
    var i := 0;
    while (i < ns.Length - 1)
        invariant 0 <= i <= ns.Length
        invariant is_sorted(ns[0..i])
        invariant forall j, k: int :: 0 <= j < i && i <= k < ns.Length ==> ns[j] <= ns[k]
        invariant is_permutation2(old(ns[..]), ns[..])
    {
        var min_idx := find_min_index(ns, i, ns.Length);
        
        // Swap elements at positions i and min_idx
        var temp := ns[i];
        ns[i] := ns[min_idx];
        ns[min_idx] := temp;
        
        i := i + 1;
    }
}