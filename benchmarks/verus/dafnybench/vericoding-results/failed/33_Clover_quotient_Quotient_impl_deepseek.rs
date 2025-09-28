use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn quotient_lemma(x: nat, y: nat, r: int, q: int)
    requires 
        y != 0,
        q * y + r == x,
        0 <= r < y,
        0 <= q
    ensures {
        let (result_r, result_q) = quotient(x, y);
        result_r == r && result_q == q
    }
{
}

proof fn quotient_zero_case(x: nat)
    requires x != 0
    ensures {
        let (r, q) = quotient(0, x);
        r == 0 && q == 0
    }
{
    assert(0 * x + 0 == 0);
}

proof fn quotient_decreases(x: nat, y: nat) 
    requires
        y != 0,
        x >= y
    ensures
        x - y < x
{}

proof fn quotient_ensures(x: nat, y: nat) 
    requires y != 0
    ensures ({
        let result = quotient(x, y);
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
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
    if x < y {
        (x as int, 0)
    } else {
        proof {
            quotient_decreases(x, y);
            quotient_ensures(x - y, y);
        }
        let (sub_r, sub_q) = quotient(x - y, y);
        (sub_r, sub_q + 1)
    }
}
// </vc-code>

fn main() {
}

}