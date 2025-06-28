// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn CountUppercase(s: String) -> (count: int)
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < s.len() && IsUpperCase(s.spec_index(i))|
{
    return 0;
}

}