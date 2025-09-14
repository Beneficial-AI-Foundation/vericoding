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
method find_min_index_helper(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s
ensures min_i >= s
ensures min_i < e
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
  min_i := s;
  var current_min_val := a[s];

  var i := s + 1;
  while i < e
    invariant s <= min_i < i <= e
    invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    invariant a[min_i] == current_min_val
  {
    if a[i] < current_min_val
    {
      min_i := i;
      current_min_val := a[i];
    }
    i := i + 1;
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
  for i := 0 to n
    invariant 0 <= i <= n
    invariant is_sorted(ns[0..i])
    invariant forall k: int :: 0 <= k < i ==> (forall l: int :: i <= l < n ==> ns[k] <= ns[l])
    invariant multiset(old(ns[..])) == multiset(ns[..])
  {
    if i < n { // Ensure i < n before calling find_min_index_helper
      var min_idx := find_min_index_helper(ns, i, n);
      if min_idx != i
      {
        var temp := ns[i];
        ns[i], ns[min_idx] := ns[min_idx], temp;
      }
    }
  }
}
// </vc-code>

