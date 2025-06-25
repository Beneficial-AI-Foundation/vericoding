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

fn rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires
        0<=offset
    ensures
        b.len()==a.len(),
        forall i::0<=i<a.len() ==> b.spec_index(i)==a.spec_index((i+offset)%a.len())
{
    return Vec::new();
}

}