// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn containsSubString(a: Vec<char>, b: Vec<char>) -> (pos: int)
    requires 0 <= b.len() <= a.len()
{
}

}