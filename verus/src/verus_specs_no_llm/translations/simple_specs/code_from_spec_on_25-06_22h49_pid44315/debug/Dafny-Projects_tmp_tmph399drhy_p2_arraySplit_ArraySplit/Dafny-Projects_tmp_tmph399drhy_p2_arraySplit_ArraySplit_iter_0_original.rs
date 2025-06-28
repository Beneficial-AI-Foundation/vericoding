// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySplit(a: Vec<int>) -> (b: Vec<int>, c: Vec<int>)
    ensures
        fresh(b),
        fresh(c),
        a.spec_index(..) == b.spec_index(..) + c.spec_index(..),
        a.len() == b.len() + c.len(),
        a.len() > 1 ==> a.len() > b.len(),
        a.len() > 1 ==> a.len() > c.len()
{
    return Vec::new();
}

}