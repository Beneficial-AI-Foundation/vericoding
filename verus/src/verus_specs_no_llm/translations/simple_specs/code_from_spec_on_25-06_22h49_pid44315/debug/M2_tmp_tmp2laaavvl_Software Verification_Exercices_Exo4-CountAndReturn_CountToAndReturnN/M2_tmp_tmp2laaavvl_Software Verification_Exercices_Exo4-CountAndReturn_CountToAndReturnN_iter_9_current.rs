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
        assert(count <= n); // Help Verus verify the invariant is maintained
    }
    assert(count >= n); // From loop exit condition: !(count < n)
    assert(count <= n); // From loop invariant
    assert(count == n); // From the two assertions above
    count
}

}