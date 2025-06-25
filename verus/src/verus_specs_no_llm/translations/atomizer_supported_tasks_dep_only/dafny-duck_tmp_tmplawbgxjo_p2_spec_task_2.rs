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

fn absx(x: Vec<int>) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall i :: 0 <= i < y.len() ==>  y.spec_index(i) == abs(x.spec_index(i))
{
    return Vec::new();
}

}