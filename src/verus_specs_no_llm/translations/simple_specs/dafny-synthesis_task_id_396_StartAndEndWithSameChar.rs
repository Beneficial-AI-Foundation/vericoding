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

fn StartAndEndWithSameChar(s: String) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s.spec_index(0) == s.spec_index(s.len() - 1)
{
    return false;
}

}