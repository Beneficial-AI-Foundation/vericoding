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

fn Reverse(a: Vec<char>) -> (b: Vec<char>, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

method Reverse(a: Vec<char>) returns (b: array<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall k :: 0 <= k < a.len() ==> b.spec_index(k) == a.spec_index((a.len()-1) - k)
{
    return Vec::new();
}

}