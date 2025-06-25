// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn random(a: int, b: int) -> r: int)
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
    requires a <= b,
             a != null,
             0 <= i < a.len() and 0 <= j < a.len()
  modifies a
    ensures a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

// SPEC 

method swap<T>(a: array<T>, i: int, j: int)
  //,
            a[i] == old(a[j]),
            a[j] == old(a[i]),
            forall|m: int| 0 <= m < a.len() and m != i and m != j ==> a[m] == old(a[m]),
            multiset(a[..]) == old(multiset(a[..]))
{
}

}