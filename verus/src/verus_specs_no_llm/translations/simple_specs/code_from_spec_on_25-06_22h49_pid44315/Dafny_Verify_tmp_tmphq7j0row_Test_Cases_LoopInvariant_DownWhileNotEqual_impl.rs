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
    let mut i = N;
    while i != 0
        invariant 
            0 <= i <= N
        decreases i
    {
        i = i - 1;
    }
    i
}

}