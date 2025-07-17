// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

spec fn spec_CountDigits(s: String) -> count: int
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < s.len() && IsDigit(s.index(i))|
;

proof fn lemma_CountDigits(s: String) -> (count: int)
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < s.len() && IsDigit(s.index(i))|
{
    0
}

}