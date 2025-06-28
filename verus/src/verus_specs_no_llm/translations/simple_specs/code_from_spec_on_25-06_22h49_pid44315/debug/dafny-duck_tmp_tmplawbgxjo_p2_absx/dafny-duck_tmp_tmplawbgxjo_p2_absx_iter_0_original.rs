// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn absx(x: Vec<int>) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall i :: 0 <= i < y.len() ==> y.spec_index(i) == abs(x.spec_index(i))
{
    return Vec::new();
}

}