// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): successor property of exp_int */
proof fn lemma_exp_succ(x: nat, y: nat)
    ensures
        exp_int(x, y + 1) == x * exp_int(x, y)
{
    // Directly unfold the recursive definition
    assert(exp_int(x, y + 1) == x * exp_int(x, y));
}

/* helper modified by LLM (iteration 2): trivial u8 bound helper */
proof fn lemma_u8_max(v: u8)
    ensures
        v as nat <= 255
{
    assert(v as nat <= 255);
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        y as nat == exp_int(2, n as nat),
        z > 0,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): iterative modular exponentiation using bounded u16 arithmetic and explicit cast/mod bridges */
    let mut i: u8 = 0;
    let zm: u16 = z as u16;
    assert(z > 0);
    assert(zm > 0);
    let mut acc: u16 = 1u16 % zm;

    // Establish base invariants
    proof {
        assert(exp_int(x as nat, 0) == 1);
        assert((acc as nat) < (z as nat));
    }

    while i < y
        invariant
            z > 0,
            (i as nat) <= (y as nat),
            acc as nat == exp_int(x as nat, i as nat) % (z as nat),
            (acc as nat) < (z as nat),
        decreases (y as nat - i as nat)
    {
        let old_acc: u16 = acc;
        let xm: u16 = x as u16;

        let prod: u16 = old_acc * xm;
        acc = prod % zm;

        proof {
            // Bounds to guarantee no overflow in u16 multiplication and correct mod bridging
            assert(z as nat <= 255);
            assert((old_acc as nat) < (z as nat));
            assert((old_acc as nat) <= 255);
            assert((x as nat) <= 255);
            assert(((old_acc as nat) * (x as nat)) <= 255 * 255);
            assert(255 * 255 <= 65535);
            assert(((old_acc as nat) * (x as nat)) <= 65535);
            // u16 multiplication equals mathematical product under the bound
            assert((prod as nat) == ((old_acc as nat) * (x as nat)));
            // u16 modulo equals nat modulo under the bounds
            assert((acc as nat) == (((prod as nat) % (z as nat))));

            // Relate old_acc to the current exponent value modulo z
            let e: nat = exp_int(x as nat, i as nat);
            assert((old_acc as nat) == (e % (z as nat)));

            // Replace prod with (e % z) * x
            assert((acc as nat) == ((((e % (z as nat)) * (x as nat)) % (z as nat))));

            // Use Euclidean division identity to cancel the modulo on the left multiplicand
            let q: nat = e / (z as nat);
            let r: nat = e % (z as nat);
            assert(e == (z as nat) * q + r);
            assert((acc as nat) == ((r * (x as nat)) % (z as nat)));
            assert(((((z as nat) * q + r) * (x as nat)) % (z as nat)) == ((r * (x as nat)) % (z as nat)));
            assert(((e * (x as nat)) % (z as nat)) == ((r * (x as nat)) % (z as nat)));
            assert((acc as nat) == ((e * (x as nat)) % (z as nat)));

            // Convert to exponent successor form
            lemma_exp_succ(x as nat, i as nat);
            assert((e * (x as nat)) % (z as nat) == exp_int(x as nat, (i as nat) + 1) % (z as nat));

            // Remainder property ensures < modulus
            assert((acc as nat) < (z as nat));
        }

        i = i + 1;
    }

    proof {
        assert(!(i < y));
        assert((i as nat) <= (y as nat));
        assert((i as nat) == (y as nat));
    }

    let res: u8 = acc as u8;
    proof {
        assert(acc as nat == exp_int(x as nat, y as nat) % (z as nat));
        assert((acc as nat) < (z as nat));
        assert(z as nat <= 255);
        assert((acc as nat) <= 254);
        assert((acc as nat) < 256);
        assert(res as nat == acc as nat);
    }
    res
}
// </vc-code>


}

fn main() {}