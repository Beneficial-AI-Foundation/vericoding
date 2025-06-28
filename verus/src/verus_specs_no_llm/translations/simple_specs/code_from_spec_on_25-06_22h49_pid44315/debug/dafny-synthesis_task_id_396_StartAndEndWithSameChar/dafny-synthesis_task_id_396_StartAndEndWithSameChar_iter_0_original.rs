// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: String) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s.spec_index(0) == s.spec_index(s.len() - 1)
{
    return false;
}

}