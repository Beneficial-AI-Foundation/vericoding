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
/* helper modified by LLM (iteration 10): inductive lemmas about exp_int and modular squaring */
proof fn exp_int_add(x: nat, a: nat, b: nat)
    ensures exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
    decreases b
{
    if b == 0 {
        assert(exp_int(x, a + 0) == exp_int(x, a));
        assert(exp_int(x, 0) == 1);
        assert(exp_int(x, a) == exp_int(x, a) * 1);
    } else {
        exp_int_add(x, a, b - 1);
        assert(exp_int(x, a + b) == x * exp_int(x, a + (b - 1)));
        assert(exp_int(x, a + (b - 1)) == exp_int(x, a) * exp_int(x, b - 1));
        assert(x * exp_int(x, a + (b - 1)) == x * (exp_int(x, a) * exp_int(x, b - 1)));
        assert(x * (exp_int(x, a) * exp_int(x, b - 1)) == (x * exp_int(x, a)) * exp_int(x, b - 1));
        assert((x * exp_int(x, a)) * exp_int(x, b - 1) == exp_int(x, a) * (x * exp_int(x, b - 1)));
        assert(x * exp_int(x, b - 1) == exp_int(x, b));
        assert(exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b));
    }
}

proof fn lemma_pow2_div(y: nat, n: nat)
    requires n > 0, y == exp_int(2, n)
    ensures (y / 2) == exp_int(2, n - 1)
    decreases n
{
    // For n > 0, exp_int(2, n) == 2 * exp_int(2, n - 1)
    assert(exp_int(2, n) == 2 * exp_int(2, n - 1));
    assert(y == exp_int(2, n));
    assert(y == 2 * exp_int(2, n - 1));
    // since y is exactly twice exp_int(2, n-1), dividing by 2 yields exp_int(2, n-1)
    assert(y / 2 == exp_int(2, n - 1));
}

proof fn lemma_modular_square(x: nat, m: nat, z: nat, r1: nat)
    requires z > 0, r1 % z == exp_int(x, m) % z
    ensures (r1 * r1) % z == exp_int(x, 2 * m) % z
    decreases m
{
    // exp_int(x, 2*m) = exp_int(x, m) * exp_int(x, m)
    exp_int_add(x, m, m);
    assert(exp_int(x, 2 * m) == exp_int(x, m) * exp_int(x, m));

    // modular arithmetic properties: reduce operands modulo z
    assert((r1 * r1) % z == ((r1 % z) * (r1 % z)) % z);
    assert(((r1 % z) * (r1 % z)) % z == ((exp_int(x, m) % z) * (exp_int(x, m) % z)) % z);
    assert(((exp_int(x, m) % z) * (exp_int(x, m) % z)) % z == (exp_int(x, m) * exp_int(x, m)) % z);

    assert((r1 * r1) % z == (exp_int(x, m) * exp_int(x, m)) % z);
    assert((r1 * r1) % z == exp_int(x, 2 * m) % z);
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
    /* code modified by LLM (iteration 10): recursive doubling with modular-square proof and safe casts */
    if n == 0 {
        // when n == 0, y == 1 and result is x % z
        let res: u8 = x % z;
        res
    } else {
        let n1: u8 = n - 1;
        let y_half: u8 = y / 2;
        let r1: u8 = mod_exp_pow2_int(x, y_half, n1, z);

        // compute square in a wider type to avoid overflow
        let prod_u32: u32 = (r1 as u32) * (r1 as u32);
        let res_u8: u8 = (prod_u32 % (z as u32)) as u8;

        proof {
            // r1 corresponds to exp_int(x, y_half) mod z
            assert((r1 as nat) % (z as nat) == exp_int(x as nat, y_half as nat) % (z as nat));

            // relate y and n to get y_half == exp_int(2, n-1)
            lemma_pow2_div(y as nat, n as nat);
            assert((y as nat) / 2 == exp_int(2, (n as nat) - 1));
            assert((y_half as nat) == (y as nat) / 2);
            assert((y_half as nat) == exp_int(2, (n as nat) - 1));

            // use modular-square lemma to lift r1^2 mod z to exp_int(x, 2*y_half) mod z
            assert(((r1 as nat) % (z as nat)) == exp_int(x as nat, y_half as nat) % (z as nat));
            lemma_modular_square(x as nat, y_half as nat, z as nat, r1 as nat);
            assert(((r1 as nat) * (r1 as nat)) % (z as nat) == exp_int(x as nat, 2 * (y_half as nat)) % (z as nat));

            // connect prod_u32 and res_u8 back to nat arithmetic used in spec
            assert((prod_u32 as nat) == (r1 as nat) * (r1 as nat));
            assert(((prod_u32 % (z as u32)) as nat) == ((r1 as nat) * (r1 as nat)) % (z as nat));

            // 2 * y_half == y because y == 2^n
            assert(2 * (y_half as nat) == y as nat);

            // final equality: res_u8 corresponds to exp_int(x, y) % z
            assert((res_u8 as nat) == exp_int(x as nat, y as nat) % (z as nat));
        }

        res_u8
    }
}

// </vc-code>


}

fn main() {}