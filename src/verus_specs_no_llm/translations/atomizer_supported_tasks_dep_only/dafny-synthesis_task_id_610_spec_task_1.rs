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

fn RemoveElement(s: Vec<int>, k: int) -> (v: Vec<int>)
    requires
        0 <= k < s.len()
    ensures
        v.len() == s.len() - 1,
        forall i :: 0 <= i < k ==> v.spec_index(i) == s.spec_index(i),
        forall i :: k <= i < v.len() ==> v.spec_index(i) == s.spec_index(i + 1)
{
    return Vec::new();
}

}