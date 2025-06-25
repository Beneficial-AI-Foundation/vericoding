// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn longestPrefix(a: Vec<int>, b: array <int>) -> (i: nat)
    ensures i <= a.len() and i <= b.len(),
            a[..i] == b[..i],
            i < a.len() and i < b.len() ==> a[i] != b[i]
{
}

}