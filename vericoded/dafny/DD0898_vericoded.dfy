method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
  assume{:axiom} false;
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
lemma multiset_concat(a: seq<int>, b: seq<int>)
ensures multiset(a + b) == multiset(a) + multiset(b)
{
}

lemma swap_is_permutation(a: seq<int>, i: int, j: int)
requires 0 <= i < |a|
requires 0 <= j < |a|
ensures is_permutation2(a, if i < j then a[..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..] 
                           else if i > j then a[..j] + [a[i]] + a[j+1..i] + [a[j]] + a[i+1..]
                           else a)
{
    if i < j {
        var b := a[..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..];
        
        // First, prove multiset(a) can be decomposed
        assert a == a[..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..];
        multiset_concat(a[..i], [a[i]] + a[i+1..j] + [a[j]] + a[j+1..]);
        multiset_concat([a[i]], a[i+1..j] + [a[j]] + a[j+1..]);
        multiset_concat(a[i+1..j], [a[j]] + a[j+1..]);
        multiset_concat([a[j]], a[j+1..]);
        
        // Now prove multiset(b) equals the same
        multiset_concat(a[..i], [a[j]] + a[i+1..j] + [a[i]] + a[j+1..]);
        multiset_concat([a[j]], a[i+1..j] + [a[i]] + a[j+1..]);
        multiset_concat(a[i+1..j], [a[i]] + a[j+1..]);
        multiset_concat([a[i]], a[j+1..]);
        
        // Multiset addition is commutative
        assert multiset([a[i]]) + multiset([a[j]]) == multiset([a[j]]) + multiset([a[i]]);
        
        calc == {
            multiset(a);
            multiset(a[..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..]);
            multiset(a[..i]) + multiset([a[i]]) + multiset(a[i+1..j]) + multiset([a[j]]) + multiset(a[j+1..]);
            multiset(a[..i]) + multiset([a[j]]) + multiset(a[i+1..j]) + multiset([a[i]]) + multiset(a[j+1..]);
            multiset(a[..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..]);
            multiset(b);
        }
    } else if i > j {
        var b := a[..j] + [a[i]] + a[j+1..i] + [a[j]] + a[i+1..];
        
        // First, prove multiset(a) can be decomposed
        assert a == a[..j] + [a[j]] + a[j+1..i] + [a[i]] + a[i+1..];
        multiset_concat(a[..j], [a[j]] + a[j+1..i] + [a[i]] + a[i+1..]);
        multiset_concat([a[j]], a[j+1..i] + [a[i]] + a[i+1..]);
        multiset_concat(a[j+1..i], [a[i]] + a[i+1..]);
        multiset_concat([a[i]], a[i+1..]);
        
        // Now prove multiset(b) equals the same
        multiset_concat(a[..j], [a[i]] + a[j+1..i] + [a[j]] + a[i+1..]);
        multiset_concat([a[i]], a[j+1..i] + [a[j]] + a[i+1..]);
        multiset_concat(a[j+1..i], [a[j]] + a[i+1..]);
        multiset_concat([a[j]], a[i+1..]);
        
        // Multiset addition is commutative
        assert multiset([a[j]]) + multiset([a[i]]) == multiset([a[i]]) + multiset([a[j]]);
        
        calc == {
            multiset(a);
            multiset(a[..j] + [a[j]] + a[j+1..i] + [a[i]] + a[i+1..]);
            multiset(a[..j]) + multiset([a[j]]) + multiset(a[j+1..i]) + multiset([a[i]]) + multiset(a[i+1..]);
            multiset(a[..j]) + multiset([a[i]]) + multiset(a[j+1..i]) + multiset([a[j]]) + multiset(a[i+1..]);
            multiset(a[..j] + [a[i]] + a[j+1..i] + [a[j]] + a[i+1..]);
            multiset(b);
        }
    } else {
        assert multiset(a) == multiset(a);
    }
}

lemma sorted_prefix_property(ns: array<int>, i: int)
requires 0 <= i <= ns.Length
requires is_sorted(ns[..i])
requires forall k :: 0 <= k < i ==> forall j :: i <= j < ns.Length ==> ns[k] <= ns[j]
ensures forall k, j :: 0 <= k < i && i <= j < ns.Length ==> ns[k] <= ns[j]
{
}
// </vc-helpers>

// <vc-spec>
method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < ns.Length
    invariant 0 <= i <= ns.Length
    invariant is_sorted(ns[..i])
    invariant is_permutation2(old(ns[..]), ns[..])
    invariant forall k, j :: 0 <= k < i && i <= j < ns.Length ==> ns[k] <= ns[j]
    {
        if i < ns.Length - 1 {
            var min_idx := find_min_index(ns, i, ns.Length);
            
            if min_idx != i {
                // Store old sequence for reasoning
                ghost var old_seq := ns[..];
                
                // Swap ns[i] with ns[min_idx]
                var temp := ns[i];
                ns[i] := ns[min_idx];
                ns[min_idx] := temp;
                
                // Prove the swap maintains permutation
                if i < min_idx {
                    assert ns[..] == old_seq[..i] + [old_seq[min_idx]] + old_seq[i+1..min_idx] + [old_seq[i]] + old_seq[min_idx+1..];
                } else if i > min_idx {
                    assert ns[..] == old_seq[..min_idx] + [old_seq[i]] + old_seq[min_idx+1..i] + [old_seq[min_idx]] + old_seq[i+1..];
                } else {
                    assert ns[..] == old_seq;
                }
                
                // Use the lemma to prove permutation is maintained
                swap_is_permutation(old_seq, i, min_idx);
                assert is_permutation2(old_seq, ns[..]);
                assert is_permutation2(old(ns[..]), old_seq);
                assert is_permutation2(old(ns[..]), ns[..]);
            }
            
            // Prove the invariants are maintained
            assert ns[i] <= ns[min_idx]; // The minimum is now at position i
            assert forall k :: i < k < ns.Length ==> ns[i] <= ns[k]; // ns[i] is minimum in range [i, ns.Length)
            
            // The sorted prefix is extended
            assert is_sorted(ns[..i+1]);
        }
        
        i := i + 1;
    }
    
    assert i == ns.Length;
    assert ns[..] == ns[..ns.Length];
}
// </vc-code>

