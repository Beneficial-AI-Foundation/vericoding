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

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires
        exists i::0<=i<a.len() && a.spec_index(i)==e
    ensures
        0<=n<a.len() && a.spec_index(n)==e,
        forall k :: 0 <= k < n ==> a.spec_index(k)!=e
{
    return 0;
}

}