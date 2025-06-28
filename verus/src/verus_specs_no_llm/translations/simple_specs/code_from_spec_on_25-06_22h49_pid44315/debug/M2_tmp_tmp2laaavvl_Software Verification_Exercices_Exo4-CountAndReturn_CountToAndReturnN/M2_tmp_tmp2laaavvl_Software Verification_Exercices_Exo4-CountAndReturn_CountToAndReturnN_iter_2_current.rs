use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountToAndReturnN(n: int) -> (r: int)
    requires
        n >= 0
    ensures
        r == n
{
    let mut count = 0;
    while count < n
        invariant
            0 <= count <= n
    {
        count = count + 1;
    }
    return count;
}

}