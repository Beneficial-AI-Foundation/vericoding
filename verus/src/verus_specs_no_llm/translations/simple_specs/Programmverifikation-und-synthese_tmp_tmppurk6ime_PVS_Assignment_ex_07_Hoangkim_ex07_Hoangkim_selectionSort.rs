// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindMin(a: Vec<int>, lo: nat) -> minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  minIdx := 0;
  assume lo <= minIdx < a.Length;
  assume forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x];
  return minIdx;
}


//ATOM
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  assume a[i] ==> old(a[j]);
  assume a[j] ==> old(a[i]);
}


// SPEC

method selectionSort(a: array<int>)
  modifies a
  //ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures sorted(a[..]
    requires
        a != null && a.len() > 0 && lo < a.len(),
        a != null && a.len() > 0 && i < a.len() && j < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x),
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        multiset(a.index(..)) == multiset(old(a.index(..)))
  //,
        sorted(a.index(..))
;

proof fn lemma_FindMin(a: Vec<int>, lo: nat) -> (minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  minIdx := 0;
  assume lo <= minIdx < a.Length;
  assume forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x];
  return minIdx;
}


//ATOM
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  assume a[i] ==> old(a[j]);
  assume a[j] ==> old(a[i]);
}


// SPEC

method selectionSort(a: array<int>)
  modifies a
  //ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures sorted(a[..])
    requires
        a != null && a.len() > 0 && lo < a.len(),
        a != null && a.len() > 0 && i < a.len() && j < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x),
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        multiset(a.index(..)) == multiset(old(a.index(..)))
  //,
        sorted(a.index(..))
{
    (0, 0, 0)
}

}