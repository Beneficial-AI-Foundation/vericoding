// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindSmallest(s: Vec<int>) -> (min: int)
    requires
        s.len() > 0
    ensures
        forall i :: 0 <= i < s.len() ==> min <= s.spec_index(i),
        exists i :: 0 <= i < s.len() && min == s.spec_index(i)
{
    return 0;
}

}