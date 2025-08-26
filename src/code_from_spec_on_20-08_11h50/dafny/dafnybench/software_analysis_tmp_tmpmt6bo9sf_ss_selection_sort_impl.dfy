// <vc-spec>
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
    var i : int := s;

    while i < e 
    decreases e - i // loop variant
    invariant s <= i <= e
    invariant s <= min_i < e
    // unnecessary invariant
    // invariant i < e ==> min_i <= i 
    invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] <= a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }

}



predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

predicate is_permutation(a:seq<int>, b:seq<int>)
decreases |a|
decreases |b|
{
    |a| == |b|  && 
    ((|a| == 0 && |b| == 0) ||  
    exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then  b[j+1..] else []))
}


// predicate is_permutation(a:seq<int>, b:seq<int>)
// decreases |a|
// decreases |b|
// {
//     |a| == |b|  && ((|a| == 0 && |b| == 0) ||  exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

// <vc-helpers>
// </vc-helpers>

method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
// </vc-spec>
// <vc-code>
{
    if ns.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < ns.Length - 1
    decreases ns.Length - i
    invariant 0 <= i <= ns.Length
    invariant forall x, y :: 0 <= x <= y < i ==> ns[x] <= ns[y]
    invariant forall x, y :: 0 <= x < i && i <= y < ns.Length ==> ns[x] <= ns[y]
    invariant multiset(ns[..]) == multiset(old(ns[..]))
    {
        var min_idx := find_min_index(ns, i, ns.Length);
        
        // Swap ns[i] and ns[min_idx]
        var temp := ns[i];
        ns[i] := ns[min_idx];
        ns[min_idx] := temp;
        
        i := i + 1;
    }
}
// </vc-code>