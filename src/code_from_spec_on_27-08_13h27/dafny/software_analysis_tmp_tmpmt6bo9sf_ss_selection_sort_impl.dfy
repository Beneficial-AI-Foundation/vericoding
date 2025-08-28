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
lemma min_index_correct(a: array<int>, s: int, e: int, min_i: int)
  requires a.Length > 0
  requires 0 <= s < a.Length
  requires e <= a.Length
  requires e > s
  requires min_i >= s
  requires min_i < e
  requires forall k: int :: s <= k < e ==> a[min_i] <= a[k]
  ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
}

lemma permutation_transitive(a: seq<int>, b: seq<int>, c: seq<int>)
  requires multiset(a) == multiset(b)
  requires multiset(b) == multiset(c)
  ensures multiset(a) == multiset(c)
{
}

lemma permutation_swap(a: seq<int>, i: int, j: int)
  requires 0 <= i < |a|
  requires 0 <= j < |a|
  ensures multiset(a) == multiset(a[i := a[j]][j := a[i]])
{
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
  var n := ns.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant is_sorted(ns[..i])
    invariant forall k: int :: i <= k < n ==> forall j: int :: 0 <= j < i ==> ns[j] <= ns[k]
    invariant multiset(old(ns[..])) == multiset(ns[..])
    decreases n - i
  {
    var min_i := i;
    var j := i + 1;
    
    while j < n
      invariant i <= min_i < n
      invariant i < j <= n
      invariant forall k: int :: i <= k < j ==> ns[min_i] <= ns[k]
      decreases n - j
    {
      if ns[j] < ns[min_i] {
        min_i := j;
      }
      j := j + 1;
    }
    
    if min_i != i {
      var temp := ns[i];
      ns[i] := ns[min_i];
      ns[min_i] := temp;
      permutation_swap(ns[..], i, min_i);
    }
    
    i := i + 1;
  }
}
// </vc-code>
