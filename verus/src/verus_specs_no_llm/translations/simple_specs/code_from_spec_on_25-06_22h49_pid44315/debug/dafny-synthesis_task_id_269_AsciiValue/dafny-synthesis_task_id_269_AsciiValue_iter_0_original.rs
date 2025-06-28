// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AsciiValue(c: char) -> (ascii: int)
    ensures
        ascii == c as int
{
    return 0;
}

}