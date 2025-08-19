//ATOM


// predicate is_permutation(a:seq<int>, b:seq<int>)
// decreases |a|
// decreases |b|
// {
//   |a| == |b| && ((|a| == 0 && |b| == 0) || exists i,j : int :: 0<=i<|a| && 0<=j<|b| && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
  multiset(a) == multiset(b)
}


//ATOM



predicate is_sorted(ss: seq<int>)
{
  forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}


//ATOM
method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
  /* code modified by LLM (iteration 1): added {:axiom} annotations to assume statements to fix compilation warnings */
  min_i := s;
  var j := s;
  while j < e
    invariant s <= j <= e
    invariant s <= min_i < e
    invariant forall k: int :: s <= k < j ==> a[min_i] <= a[k]
  {
    if a[j] < a[min_i] {
      min_i := j;
    }
    j := j + 1;
  }
}


//ATOM

predicate is_permutation(a:seq<int>, b:seq<int>)
{
  |a| == |b| && 
  ((|a| == 0 && |b| == 0) || 
  exists i,j : int :: 0<=i<|a| && 0<=j<|b| && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then b[j+1..] else []))
}


//IMPL selection_sort

method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{
  if ns.Length <= 1 {
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 1): added ghost variable to track original array contents for permutation proof */
  ghost var original := ns[..];
  
  while i < ns.Length - 1
    invariant 0 <= i <= ns.Length
    invariant is_permutation2(original, ns[..])
    invariant forall k1, k2: int :: 0 <= k1 <= k2 < i ==> ns[k1] <= ns[k2]
    invariant forall k1, k2: int :: 0 <= k1 < i && i <= k2 < ns.Length ==> ns[k1] <= ns[k2]
  {
    var min_idx := find_min_index(ns, i, ns.Length);
    
    if min_idx != i {
      /* code modified by LLM (iteration 1): added ghost variable to capture pre-swap state for permutation proof */
      ghost var pre_swap := ns[..];
      var temp := ns[i];
      ns[i] := ns[min_idx];
      ns[min_idx] := temp;
      
      /* code modified by LLM (iteration 1): assertion to help prove permutation is preserved after swap */
      assert multiset(pre_swap) == multiset(ns[..]);
    }
    
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): final assertion to help prove postconditions */
  assert is_permutation2(original, ns[..]);
}