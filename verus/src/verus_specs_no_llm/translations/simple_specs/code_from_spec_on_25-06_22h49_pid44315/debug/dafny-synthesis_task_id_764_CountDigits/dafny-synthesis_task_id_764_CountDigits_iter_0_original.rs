// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn CountDigits(s: String) -> (count: int)
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < s.len() && IsDigit(s.spec_index(i))|
{
    return 0;
}

}