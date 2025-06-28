use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot1(n: int) -> (r: int) //Cost O(root n)
    requires
        n >= 0
    ensures
        r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
    let mut r = 0;
    while r * r <= n
        invariant
            r >= 0,
            r * r <= n,
        decreases n - r * r
    {
        if (r + 1) * (r + 1) > n {
            break;
        }
        r = r + 1;
    }
    r
}

}