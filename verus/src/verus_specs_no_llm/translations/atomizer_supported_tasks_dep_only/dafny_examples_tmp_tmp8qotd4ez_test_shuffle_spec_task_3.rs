// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn random(a: int, b: int) -> (r: int)
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
        a.spec_index(i) == old(a.spec_index(j)),
        a.spec_index(j) == old(a.spec_index(i)),
        forall m :: 0 <= m < a.len() && m != i && m != j ==> a.spec_index(m) == old(a.spec_index(m)),
        multiset(a.spec_index(..)) == old(multiset(a.spec_index(..)))
{
    return (0, 0, 0);
}

}