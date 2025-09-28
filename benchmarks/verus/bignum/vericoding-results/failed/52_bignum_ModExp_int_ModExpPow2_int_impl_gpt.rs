// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

fn mod_exp_pow2_int(x: nat, y: nat, n: nat, z: nat) -> (res: nat)
    requires 
        y == exp_int(2, n),
        z > 0,
    ensures res == exp_int(x, y) % z
    decreases n
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add lemmas for exponent successor and modular multiplication congruence */
proof fn lemma_exp_succ(x: nat, y: nat)
    ensures exp_int(x, y + 1) == x * exp_int(x, y)
    decreases y
{
    reveal(exp_int);
    assert(y + 1 != 0);
    assert(((y + 1) - 1) as nat == y);
}

proof fn lemma_mod_mul_left_preserves_mod(a: nat, b: nat, m: nat)
    requires m > 0
    ensures ((a % m) * b) % m == (a * b) % m
{
    let q = a / m;
    let r = a % m;
    assert(a == q * m + r);
    // (q*m) is a multiple of m, hence ((q*m) * b) % m == 0
    assert(((q * m) * b) % m == 0);
    // From the above, SMT can derive congruence of multiplication modulo m
    assert(((a % m) * b) % m == (r * b) % m);
    assert((a * b) % m == ((q * m + r) * b) % m);
}

// </vc-helpers>

// <vc-spec>
fn mod_exp_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        (y as nat) < exp_int(2nat, (n as nat) + 1nat),
        (z as nat) > 1,
    ensures (res as nat) == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): strengthen invariants, add modular-multiplication lemma use, and add bounds to avoid overflow */
    let zu32: u32 = z as u32;
    let xu32: u32 = x as u32;

    assert(zu32 > 0u32); // from requires (z as nat) > 1
    assert(zu32 <= 255u32); // since z: u8
    assert(xu32 <= 255u32); // since x: u8

    let mut res_u32: u32 = 1u32 % zu32;
    let mut i: u8 = 0u8;

    while i < y
        invariant
            (i as nat) <= (y as nat),
            (z as nat) > 1,
            res_u32 < zu32,
            (res_u32 as nat) == exp_int(x as nat, i as nat) % (z as nat)
        decreases (y as nat) - (i as nat)
    {
        let old_res: u32 = res_u32;
        let old_i: u8 = i;

        // Prove bounds to avoid overflow in multiplication
        assert(old_res < zu32); // from invariant
        assert(zu32 <= 255u32);
        assert(old_res < 256u32);
        assert(xu32 < 256u32);

        let prod: u32 = old_res * xu32; // safe: both operands < 256 => product < 65536 << u32::MAX
        let rem: u32 = prod % zu32;
        res_u32 = rem;

        // Update the spec relation using modular arithmetic properties
        proof {
            // Use that res_old equals exp(x, i) % z
            assert((old_res as nat) == exp_int(x as nat, old_i as nat) % (z as nat));
            // Show ((exp % z) * x) % z == (exp * x) % z
            lemma_mod_mul_left_preserves_mod(exp_int(x as nat, old_i as nat), x as nat, z as nat);
            // exp(x, i+1) = x * exp(x, i)
            lemma_exp_succ(x as nat, old_i as nat);
        }

        // Increment i safely
        assert(i < 255u8); // since i < y and y <= 255
        i = i + 1;
    }

    assert((i as nat) == (y as nat));
    assert(res_u32 < zu32);
    assert(zu32 <= 255u32);
    assert(res_u32 < 256u32);

    let res: u8 = res_u32 as u8;
    res
}
// </vc-code>


}

fn main() {}