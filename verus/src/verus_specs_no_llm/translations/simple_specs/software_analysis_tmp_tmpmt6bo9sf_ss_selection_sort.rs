// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_permutation(a: Seq<int>, b: Seq<int>, j: int :: 0<=i<|a| && 0<=j<|b| && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

predicate is_permutation2(a: Seq<int>, b: Seq<int>) -> bool {
    multiset(a) == multiset(b)
}
spec fn is_sorted(ss: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < ss.len() ==> ss.index(i) <= ss.index(j)
}
spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len() && 
  ((a.len() == 0 && b.len() == 0) | 
  exists |i: int, j: int| 0<=i<.len()a && 0<=j<.len()b && a.index(i) == b.index(j) && is_permutation(a.index(0..i) + if i < .len()a then a.index(i+1..) else [], b.index(0..j) + if j < .len()b| then b.index(j+1..) else []))
}

spec fn spec_find_min_index(a: Vec<int>, s: int, e: int) -> min_i: int)
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



method selection_sort(ns: array<int>
    requires
        a.len() > 0,
        0 <= s < a.len(),
        e <= a.len(),
        e > s,
        ns.len() >= 0
    ensures
        min_i >= s,
        min_i < e,
        forall |k: int| s <= k < e ==> a.index(min_i) <= a.index(k),
        is_sorted(ns.index(..)),
        is_permutation2(old(ns.index(..)), ns.index(..))
modifies ns
;

proof fn lemma_find_min_index(a: Vec<int>, s: int, e: int) -> (min_i: int)
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

predicate is_permutation(a:seq<int>, b: Seq<int>, j: int :: 0<=i<|a| && 0<=j<|b| && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then b[j+1..] else []))
}


// SPEC



method selection_sort(ns: Vec<int>)
    requires
        a.len() > 0,
        0 <= s < a.len(),
        e <= a.len(),
        e > s,
        ns.len() >= 0
    ensures
        min_i >= s,
        min_i < e,
        forall |k: int| s <= k < e ==> a.index(min_i) <= a.index(k),
        is_sorted(ns.index(..)),
        is_permutation2(old(ns.index(..)), ns.index(..))
modifies ns
{
    (0, Seq::empty(), 0, Vec::new())
}

}