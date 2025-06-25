// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn CountUppercase(s: String) -> (count: int)
    ensures count >= 0,
            count ==  set i: int .len() 0 <= i < s.len() and IsUpperCase(s[i])|
{
}

}