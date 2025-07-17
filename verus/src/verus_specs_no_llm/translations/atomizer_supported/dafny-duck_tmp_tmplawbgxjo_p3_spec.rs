// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(x: Vec<nat>) -> y:nat) 
// for index loop problems
requires x.Length > 0
// ensuring that we maintain y as greater than the elements in the array 
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
// ensuring that the return value is in the array
ensures y in x[..]
{
}


// SPEC 

method Main(
    requires
        x.len() > 0
// ensuring that we maintain y as greater than the elements in the array
    ensures
        forall |j: int| 0 <= j < x.len() ==> y >= x.index(j)
// ensuring that the return value is in the array,
        y in x.index(..)
;

proof fn lemma_max(x: Vec<nat>) -> (y: nat) 
// for index loop problems
requires x.Length > 0
// ensuring that we maintain y as greater than the elements in the array 
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
// ensuring that the return value is in the array
ensures y in x[..]
{
}


// SPEC 

method Main()
    requires
        x.len() > 0
// ensuring that we maintain y as greater than the elements in the array
    ensures
        forall |j: int| 0 <= j < x.len() ==> y >= x.index(j)
// ensuring that the return value is in the array,
        y in x.index(..)
{
    0
}

}