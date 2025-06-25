// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountCharacters(s: String) -> (count: int)
    ensures count >= 0,
            count == s.len()
{
}

}