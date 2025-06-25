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