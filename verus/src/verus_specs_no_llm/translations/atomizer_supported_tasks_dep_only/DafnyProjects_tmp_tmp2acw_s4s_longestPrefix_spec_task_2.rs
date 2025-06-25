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

fn longestPrefix(a: Vec<int>, b: array <int>) -> (i: nat)
    ensures
        i <= a.len() && i <= b.len(),
        a.spec_index(..i) == b.spec_index(..i),
        i < a.len() && i < b.len() ==> a.spec_index(i) != b.spec_index(i)
{
    return 0;
}

}