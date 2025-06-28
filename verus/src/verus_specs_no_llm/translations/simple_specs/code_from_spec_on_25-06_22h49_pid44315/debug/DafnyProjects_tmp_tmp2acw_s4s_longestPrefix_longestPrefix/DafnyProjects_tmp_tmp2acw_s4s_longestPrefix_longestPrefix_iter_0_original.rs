// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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