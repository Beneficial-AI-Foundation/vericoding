use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_mul_nonneg(a: int, b: int)
    requires 0 <= a, 0 <= b
    ensures 0 <= a * b
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
    let x_int = x as int;
    let y_int = y as int;

    let mut q: int = 0;
    let mut r: int = x_int;

    while r >= y_int
        invariant
            q * y_int + r == x_int,
            0 <= r,
            0 <= q,
            y_int > 0,
        decreases r
    {
        q = q + 1;
        r = r - y_int;
        assert(q * y_int + r == (q - 1) * y_int + y_int + r - y_int);
        assert(q * y_int + r == (q - 1) * y_int + r);
        lemma_mul_nonneg(q as int, y_int);
    }

    assert(r < y_int);
    assert(q * y_int + r == x_int);
    assert(0 <= r);
    assert(0 <= q);

    (r, q)
}
// </vc-code>

fn main() {
}

}