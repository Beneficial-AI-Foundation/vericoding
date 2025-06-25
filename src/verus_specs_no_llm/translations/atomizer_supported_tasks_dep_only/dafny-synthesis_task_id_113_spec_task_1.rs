// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn IsInteger(s: String) -> (result: bool)
    ensures result <==> (s.len() > 0) and (forall|i: int| 0 <= i < s.len() ==> IsDigit(s[i]))
{
}

}