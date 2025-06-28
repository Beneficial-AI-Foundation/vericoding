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
    let mut count: int = 0;
    while count < n
        invariant
            0 <= count <= n,
        decreases
            n - count,
    {
        count = count + 1;
        // Prove that the invariant is maintained
        assert(count <= n) by {
            // Since we entered the loop, count < n before increment
            // After increment, count <= n holds
        };
    }
    // After loop exit, we have !(count < n), which means count >= n
    // Combined with the invariant count <= n, we get count == n
    assert(count >= n);
    assert(count <= n);
    assert(count == n);
    count
}

}