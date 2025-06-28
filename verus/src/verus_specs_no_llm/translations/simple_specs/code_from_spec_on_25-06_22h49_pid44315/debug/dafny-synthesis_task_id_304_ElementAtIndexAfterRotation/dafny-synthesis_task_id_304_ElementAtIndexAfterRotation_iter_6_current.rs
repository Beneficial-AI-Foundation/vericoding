use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> int
    requires
        n >= 0,
        0 <= index < l.len(),
        l.len() > 0
{
    let len = l.len() as int;
    let adjusted_index = (index - n % len + len) % len;
    l.spec_index(adjusted_index)
}

}