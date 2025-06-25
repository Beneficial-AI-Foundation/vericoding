// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsDecimalWithTwoPrecision(s: String) -> (result: bool)
    ensures result ==> (exists|i: int| 0 <= i < s.len() and s[i] == '.' and s.len() - i - 1 == 2),
            !result ==> !(exists|i: int| 0 <= i < s.len() and s[i] == '.' and s.len() - i - 1 == 2)
{
}

}