use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma for division properties
proof fn div_mod_properties(x: nat, y: nat)
    requires y != 0
    ensures 
        x as int / y as int * y as int + x as int % y as int == x as int,
        0 <= x as int % y as int,
        x as int % y as int < y as int,
        0 <= x as int / y as int
{
    // Verus automatically proves division and modulo properties
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let q = x as int / y as int;
    let r = x as int % y as int;
    
    proof {
        div_mod_properties(x, y);
    }
    
    (r, q)
}
// </vc-code>

fn main() {
}

}