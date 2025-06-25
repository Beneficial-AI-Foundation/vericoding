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

fn concat(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len()==b.len()+a.len(),
        forall k :: 0 <= k < a.len() ==> c.spec_index(k) == a.spec_index(k),
        forall k :: 0 <= k < b.len() ==> c.spec_index(k+a.len()) == b.spec_index(k)
{
    return Vec::new();
}

}