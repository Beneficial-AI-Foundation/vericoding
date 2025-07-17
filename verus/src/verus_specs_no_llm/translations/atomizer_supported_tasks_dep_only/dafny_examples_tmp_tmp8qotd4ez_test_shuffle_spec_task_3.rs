// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_random(a: int, b: int) -> r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

// SPEC 

method swap<T>(a: array<T>, i: int, j: int)
  // requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]
    requires
        a <= b,
        a != null,
        0 <= i < a.len() && 0 <= j < a.len()
  modifies a
    ensures
        a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

// SPEC 

method swap<T>(a: array<T>, i: int, j: int)
  //,
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        forall |m: int| 0 <= m < a.len() && m != i && m != j ==> a.index(m) == old(a.index(m)),
        multiset(a.index(..)) == old(multiset(a.index(..)))
;

proof fn lemma_random(a: int, b: int) -> (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

// SPEC 

method swap<T>(a: array<T>, i: int, j: int)
  // requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
    requires
        a <= b,
        a != null,
        0 <= i < a.len() && 0 <= j < a.len()
  modifies a
    ensures
        a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

// SPEC 

method swap<T>(a: array<T>, i: int, j: int)
  //,
        a.index(i) == old(a.index(j)),
        a.index(j) == old(a.index(i)),
        forall |m: int| 0 <= m < a.len() && m != i && m != j ==> a.index(m) == old(a.index(m)),
        multiset(a.index(..)) == old(multiset(a.index(..)))
{
    (0, 0, 0)
}

}