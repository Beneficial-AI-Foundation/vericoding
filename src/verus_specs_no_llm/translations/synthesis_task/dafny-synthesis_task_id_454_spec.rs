// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ContainsZ(s: String) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < s.len() and (s[i] == 'z' or s[i] == 'Z'))
{
}

}