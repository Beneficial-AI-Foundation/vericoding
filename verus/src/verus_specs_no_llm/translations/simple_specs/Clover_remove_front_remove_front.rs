// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn remove_front(a: Vec<int>) -> (c: Vec<int>)
    requires
        a.len()>0
    ensures
        a.spec_index(1..) == c.spec_index(..)
{
    return Vec::new();
}

}