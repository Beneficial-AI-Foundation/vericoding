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

fn LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires
        n >= 0
    ensures
        forall i :: 0 <= i < lucid.len() ==> lucid.spec_index(i) % 3 == 0,
        forall i :: 0 <= i < lucid.len() ==> lucid.spec_index(i) <= n,
        forall i, j :: 0 <= i < j < lucid.len() ==> lucid.spec_index(i) < lucid.spec_index(j)
{
    return Seq::empty();
}

}