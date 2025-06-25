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

fn arraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len()==b.len()
    ensures
        c.len()==a.len(),
        forall i:: 0 <= i< a.len()==> a.spec_index(i) + b.spec_index(i)==c.spec_index(i)
{
    return Vec::new();
}

}