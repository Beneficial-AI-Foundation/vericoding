use builtin::*;
use builtin_macros::*;

verus! {

fn AsciiValue(c: char) -> (ascii: int)
    ensures
        ascii == c as int
{
    c as int
}

fn main() {
}

}