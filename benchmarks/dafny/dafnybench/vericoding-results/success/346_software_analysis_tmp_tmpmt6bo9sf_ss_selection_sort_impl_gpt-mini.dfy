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
lemma SwapSeqPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
  if i == j {
    // trivial
  } else if i < j {
    var p := s[..i];
    var a := s[i];
    var mid := s[i+1..j];
    var b := s[j];
    var suf := s[j+1..];
    assert s == p + [a] + mid + [b] + suf;
    assert s[i := b][j := a] == p + [b] + mid + [a] + suf;
    calc {
      multiset(s[i := b][j := a]);
      == { }
      multiset(p) + multiset([b]) + multiset(mid) + multiset([a]) + multiset(suf);
      == { }
      multiset(p) + multiset([a]) + multiset(mid) + multiset([b]) + multiset(suf);
      == { }
      multiset(s);
    }
  } else {
    // i > j
    SwapSeqPreservesMultiset(s, j, i);
  }
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
  var n := ns.Length;
  ghost var orig := ns[..];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant is_sorted(ns[..i])
    invariant forall k, l :: 0 <= k < i && i <= l < n ==> ns[k] <= ns[l]
    invariant multiset(ns[..]) == multiset(orig)
    decreases n - i
  {
    var m := i;
    var j := i + 1;
    while j < n
      invariant i <= j && j <= n
      invariant i <= m && m < n
      invariant forall k :: i <= k < j ==> ns[m] <= ns[k]
      invariant is_sorted(ns[..i])
      invariant forall k, l :: 0 <= k < i && i <= l < n ==> ns[k] <= ns[l]
      invariant multiset(ns[..]) == multiset(orig)
      decreases n - j
    {
      if ns[j] < ns[m] {
        m := j;
      }
      j := j + 1;
    }

    // save the current sequence and related facts before modifying the array
    ghost var s := ns[..];
    ghost var vi := s[i];
    ghost var vm := s[m];

    // facts from the loop invariants about the old sequence s
    assert is_sorted(s[..i]);
    assert forall k, l :: 0 <= k < i && i <= l < n ==> s[k] <= s[l];
    // m is minimal in the suffix [i..n)
    assert forall k :: i <= k < n ==> s[m] <= s[k];

    // swap ns[i] and ns[m]
    var tmp := ns[m];
    ns[m] := ns[i];
    ns[i] := tmp;

    // relate array after swap to sequence with two updates
    assert ns[..] == s[i := vm][m := vi];

    // swapping sequence elements preserves multiset
    SwapSeqPreservesMultiset(s, i, m);
    // now multiset(ns[..]) == multiset(s)
    assert multiset(ns[..]) == multiset(s);
    // and by outer invariant multiset(s) == multiset(orig), so preserved
    assert multiset(ns[..]) == multiset(orig);

    // Prove is_sorted(ns[..i+1]):
    // - For indices < i, ordering unchanged.
    // - For any k < i, ns[k] <= ns[i] because s[k] <= s[m] and ns[i] == s[m].
    assert forall k :: 0 <= k < i ==> ns[k] == s[k];
    assert forall k :: 0 <= k < i ==> s[k] <= s[m];
    assert forall k :: 0 <= k < i ==> ns[k] <= ns[i];

    // combine to get full sortedness of prefix of length i+1
    assert is_sorted(ns[..i+1]);
    
    // Prove the ordering invariant for next iteration:
    // forall k < i+1 and l >= i+1, ns[k] <= ns[l]
    assert forall k, l :: 0 <= k < i+1 && i+1 <= l < n ==>
      if k < i then ns[k] <= ns[l] else ns[i] <= ns[l];
    {
      // For k < i: use s[k] <= s[l] (holds for l>=i) and element equalities
      // For k == i: ns[i] == s[m] and s[m] <= s[l] for l>=i+1
    }

    i := i + 1;
  }

  // postconditions follow from loop invariants
  assert is_sorted(ns[..]);
  assert multiset(ns[..]) == multiset(orig);
}
// </vc-code>

