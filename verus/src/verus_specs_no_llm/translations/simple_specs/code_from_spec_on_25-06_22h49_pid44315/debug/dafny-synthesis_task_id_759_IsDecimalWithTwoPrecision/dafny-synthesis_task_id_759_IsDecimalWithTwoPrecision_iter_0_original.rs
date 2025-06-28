// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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