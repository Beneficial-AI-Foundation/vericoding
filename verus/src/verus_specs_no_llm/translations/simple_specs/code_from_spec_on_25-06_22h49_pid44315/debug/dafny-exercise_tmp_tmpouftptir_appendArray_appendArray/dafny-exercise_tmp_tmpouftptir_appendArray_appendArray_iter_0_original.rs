// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn appendArray(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len() == a.len() + b.len(),
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) == c.spec_index(i),
        forall i :: 0 <= i < b.len() ==> b.spec_index(i) == c.spec_index(a.len() + i)
{
    return Vec::new();
}

}