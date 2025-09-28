use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn div_mod_properties(x: nat, y: nat)
    requires y != 0
    ensures x / y * y + x % y == x
    ensures 0 <= x % y < y
    ensures 0 <= x / y
{
}
// </vc-helpers>

// <vc-spec>
proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// <vc-code>
{
    let q = (x / y) as int;
    let r = (x % y) as int;
    
    proof {
        div_mod_properties(x, y);
    }
    
    (r, q)
}
// </vc-code>

fn main() {
}

}