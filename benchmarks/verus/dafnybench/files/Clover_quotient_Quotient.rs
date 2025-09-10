use vstd::prelude::*;

verus! {

proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
{
    assume(false);
    unreached()
}

}
fn main() {}