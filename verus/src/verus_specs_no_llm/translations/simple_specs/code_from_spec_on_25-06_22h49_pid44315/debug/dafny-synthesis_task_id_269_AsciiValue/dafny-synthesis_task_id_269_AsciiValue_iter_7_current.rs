use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AsciiValue(c: char) -> (ascii: int)
    ensures
        ascii == c as int
{
    let result = c as int;
    proof {
        // The cast operation is deterministic, so the result equals c as int
        assert(result == c as int);
    }
    result
}

}