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
lemma selection_sort_invariant_helper(ns: array<int>, i: int)
requires 0 <= i < ns.Length
requires is_sorted(ns[0..i])
requires forall k: int :: 0 <= k < i ==> forall j: int :: i <= j < ns.Length ==> ns[k] <= ns[j]
ensures forall k: int :: 0 <= k < i ==> forall j: int :: i <= j < ns.Length ==> ns[k] <= ns[j]
{
}

lemma min_element_property(ns: array<int>, i: int, min_i: int)
requires 0 <= i < ns.Length
requires i <= min_i < ns.Length
requires forall k: int :: i <= k < ns.Length ==> ns[min_i] <= ns[k]
requires is_sorted(ns[0..i])
requires forall k: int :: 0 <= k < i ==> forall j: int :: i <= j < ns.Length ==> ns[k] <= ns[j]
ensures forall k: int :: 0 <= k < i ==> ns[k] <= ns[min_i]
{
}

lemma swap_preserves_permutation(ns: array<int>, old_ns: seq<int>, i: int, min_i: int)
requires 0 <= i < ns.Length
requires i <= min_i < ns.Length
requires old_ns == ns[..]
ensures i == min_i ==> is_permutation2(old_ns, ns[..])
ensures i < min_i ==> is_permutation2(old_ns, ns[0..i] + [ns[min_i]] + ns[i+1..min_i] + [ns[i]] + ns[min_i+1..])
{
    if i == min_i {
        assert old_ns == ns[..];
        assert is_permutation2(old_ns, ns[..]);
    } else {
        assert i < min_i;
        assert old_ns == ns[0..i] + [ns[i]] + ns[i+1..min_i] + [ns[min_i]] + ns[min_i+1..];
        var swapped := ns[0..i] + [ns[min_i]] + ns[i+1..min_i] + [ns[i]] + ns[min_i+1..];
        assert multiset(old_ns) == multiset(swapped);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  
  while i < ns.Length - 1
  invariant 0 <= i <= ns.Length
  invariant is_sorted(ns[0..i])
  invariant forall k: int :: 0 <= k < i ==> forall j: int :: i <= j < ns.Length ==> ns[k] <= ns[j]
  invariant is_permutation2(old(ns[..]), ns[..])
  {
    var min_i := find_min_index(ns, i, ns.Length);
    
    min_element_property(ns, i, min_i);
    
    if i != min_i {
      var old_ns := ns[..];
      swap_preserves_permutation(ns, old_ns, i, min_i);
      var temp := ns[i];
      ns[i] := ns[min_i];
      ns[min_i] := temp;
      
      assert is_permutation2(old_ns, ns[..]);
    }
    
    i := i + 1;
  }
}
// </vc-code>
