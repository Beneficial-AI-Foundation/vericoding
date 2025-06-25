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

fn IsDecimalWithTwoPrecision(s: String) -> (result: bool)
    ensures
        result ==> (exists i :: 0 <= i < s.len() && s.spec_index(i) == '.' && s.len() - i - 1 == 2),
        !result ==> !(exists i :: 0 <= i < s.len() && s.spec_index(i) == '.' && s.len() - i - 1 == 2)
{
    return false;
}

}