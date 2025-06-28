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
        decreases n - r*r
    {
        assert(r*r < (r+1)*(r+1)); // This helps prove decreases clause
        assert((r+1)*(r+1) <= n); // Loop condition
        assert(r*r < n); // Follows from above two assertions
        r = r + 1;
    }
    // At this point: r >= 0, r*r <= n, and (r+1)*(r+1) > n
    // Which gives us exactly what we need: r*r <= n < (r+1)*(r+1)
    r
}

}