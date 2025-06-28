use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot2(n: int) -> (r: int) //Cost O(n)
    requires
        n>=0
    ensures
        r>=0 && r*r <= n < (r+1)*(r+1)
{
    let mut r = 0;
    while (r+1)*(r+1) <= n
        invariant
            r >= 0,
            r*r <= n,
            r <= n, // This helps with termination
        decreases n - r
    {
        r = r + 1;
    }
    r
}

}