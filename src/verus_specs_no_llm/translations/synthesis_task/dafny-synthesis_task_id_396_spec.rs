// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn StartAndEndWithSameChar(s: String) -> (result: bool)
    requires s.len() > 0
    ensures result <==> s[0] == s[s.len() - 1]
{
}

}