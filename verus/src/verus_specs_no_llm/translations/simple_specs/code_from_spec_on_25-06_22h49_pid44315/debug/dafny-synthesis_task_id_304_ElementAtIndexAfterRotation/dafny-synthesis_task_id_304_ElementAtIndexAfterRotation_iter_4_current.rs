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
    ensures
        ElementAtIndexAfterRotation(l, n, index) == l.spec_index((index - n + l.len()) % l.len())
{
    l.spec_index((index - n + l.len()) % l.len())
}

}