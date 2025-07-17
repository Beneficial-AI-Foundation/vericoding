// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AsciiValue(c: char) -> ascii: int
    ensures
        ascii == c as int
;

proof fn lemma_AsciiValue(c: char) -> (ascii: int)
    ensures
        ascii == c as int
{
    0
}

}