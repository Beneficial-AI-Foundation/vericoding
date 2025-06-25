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

fn arrayUpToN(n: int) -> (a: Vec<int>)
    requires
        n >= 0
    ensures
        a.len() == n,
        forall j :: 0 < j < n ==> a.spec_index(j) >= 0,
        forall j, k : int :: 0 <= j <= k < n ==> a.spec_index(j) <= a.spec_index(k)
{
    return Vec::new();
}

}