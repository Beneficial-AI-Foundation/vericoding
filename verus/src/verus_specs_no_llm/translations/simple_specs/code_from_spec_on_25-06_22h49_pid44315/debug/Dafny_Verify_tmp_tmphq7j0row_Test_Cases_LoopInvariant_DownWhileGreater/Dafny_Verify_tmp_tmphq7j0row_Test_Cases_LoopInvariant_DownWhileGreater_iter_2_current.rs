use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DownWhileGreater(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == 0
{
    0
}

}