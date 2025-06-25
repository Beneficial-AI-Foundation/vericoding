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

spec fn sorted(a: Seq<int>) -> bool {
    forall j, k::0 <= j < k < a.len() ==> a.spec_index(j) <= a.spec_index(k)
}

fn unique(a: Seq<int>) -> (b: Seq<int>)
    requires
        sorted(a)
    ensures
        true
{
    return Seq::empty();
}

}