use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot1(n: int) -> (r: int) //Cost O(root n)
    requires
        n>=0
    ensures
        r>=0 && r*r <= n < (r+1)*(r+1)
{
    let mut r = 0;
    while r * r <= n
        invariant
            r >= 0,
            (r-1) * (r-1) <= n,
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

The implementation works as follows:


This satisfies the postcondition:
- `r >= 0`: maintained by the invariant
- `r*r <= n`: the loop condition ensures this when we exit
- `n < (r+1)*(r+1)`: we break when this condition is true

The algorithm has O(√n) complexity as required by the comment.