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

//ATOM_PLACEHOLDER_swap
  
//ATOM_PLACEHOLDER_getAllShuffledDataEntries

// ATOM 

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}


//ATOM_PLACEHOLDER_in_set_of_seq//ATOM_PLACEHOLDER_subset_set_of_seq// SPEC 
  
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: Seq<T>)
    requires
        a <= b,
        m_workList.len() > 0
//
    ensures
        a <= b ==> a <= r <= b
//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

//ATOM_PLACEHOLDER_swap
  
//ATOM_PLACEHOLDER_getAllShuffledDataEntries

// ATOM 

function set_of_seq<T>(s: seq<T>): set<T>,
        set_of_seq(avoidSet) < set_of_seq(m_workList.spec_index(..)) ==> e !in avoidSet
//,
        avoidSet < m_workList.spec_index(..) ==> e in m_workList.spec_index(..)
{
    return (0, Seq::empty());
}

}