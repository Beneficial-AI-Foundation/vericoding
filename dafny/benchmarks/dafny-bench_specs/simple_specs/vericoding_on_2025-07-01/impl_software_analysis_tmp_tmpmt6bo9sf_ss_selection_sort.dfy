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
  min_i := 0;
  assume min_i >= s;
  assume min_i < e;
  assume forall k: int :: s <= k < e ==> a[min_i] <= a[k];
  return min_i;
}

//ATOM

predicate is_permutation(a:seq<int>, b:seq<int>)
{
  |a| == |b| && 
  ((|a| == 0 && |b| == 0) || 
  exists i,j : int :: 0<=i<|a| && 0<=j<|b| && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then b[j+1..] else []))
}


// SPEC



method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{
}