use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DownWhileNotEqual(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == 0
{
    0
}

}