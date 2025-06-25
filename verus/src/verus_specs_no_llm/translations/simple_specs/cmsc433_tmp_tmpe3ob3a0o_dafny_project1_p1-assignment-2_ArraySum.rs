// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len() && 
    forall i : int :: 0 <= i < c.len() ==> c.spec_index(i) == a.spec_index(i) + b.spec_index(i) // TODO
{
    return Vec::new();
}

}