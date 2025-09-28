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
proof fn exp_int_unfold(x: nat, y: nat)
    requires y > 0
    ensures exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
    decreases y
{
}

proof fn exp_int_mult(x: nat, a: nat, b: nat)
    ensures exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
    decreases a
{
    if a == 0 {
        assert(exp_int(x, 0 + b) == exp_int(x, b));
        assert(exp_int(x, 0) == 1);
        assert(exp_int(x, a) * exp_int(x, b) == 1 * exp_int(x, b));
    } else {
        exp_int_mult(x, (a - 1) as nat, b);
        assert(exp_int(x, ((a - 1) as nat) + b) == exp_int(x, (a - 1) as nat) * exp_int(x, b));
        assert(exp_int(x, a) == x * exp_int(x, (a - 1) as nat));
        assert(exp_int(x, a + b) == x * exp_int(x, ((a + b) - 1) as nat));
        assert(((a + b) - 1) as nat == ((a - 1) as nat) + b);
        assert(exp_int(x, a) * exp_int(x, b) == x * exp_int(x, (a - 1) as nat) * exp_int(x, b));
        proof {
            assert(x * exp_int(x, (a - 1) as nat) * exp_int(x, b) == x * (exp_int(x, (a - 1) as nat) * exp_int(x, b)));
        }
        assert(x * (exp_int(x, (a - 1) as nat) * exp_int(x, b)) == x * exp_int(x, ((a - 1) as nat) + b));
        assert(x * exp_int(x, ((a - 1) as nat) + b) == x * exp_int(x, ((a + b) - 1) as nat));
    }
}

/* helper modified by LLM (iteration 10): added base case proof for exp_int(x,1) */
proof fn exp_int_base_case(x: nat)
    ensures exp_int(x, 1) == x
{
    assert(exp_int(x, 1) == x * exp_int(x, 0));
    assert(exp_int(x, 0) == 1);
    assert(x * 1 == x);
}

/* helper modified by LLM (iteration 10): fixed modular arithmetic property */
proof fn mod_mult_assoc(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    let a_mod = a % m;
    let b_mod = b % m;
    assert(a == (a / m) * m + a_mod);
    assert(b == (b / m) * m + b_mod);
    proof {
        assert((a * b) % m == (((a / m) * m + a_mod) * ((b / m) * m + b_mod)) % m);
        assert((((a / m) * m + a_mod) * ((b / m) * m + b_mod)) % m == (a_mod * b_mod) % m);
        assert((a_mod * b_mod) % m == ((a % m) * (b % m)) % m);
    }
}

/* helper modified by LLM (iteration 10): fixed mod_exp_helper with proper arithmetic */
proof fn mod_exp_helper(x: nat, y: nat, z: nat)
    requires 
        z > 0,
        y > 0
    ensures (exp_int(x, y) % z) == ((x % z) * (exp_int(x, (y - 1) as nat) % z)) % z
    decreases y
{
    if y == 1 {
        exp_int_base_case(x);
        assert(exp_int(x, 1) == x);
        assert(exp_int(x, 0) == 1nat);
        proof {
            assert((x % z) * (1nat % z) == (x % z) * 1nat);
        }
        assert((x % z) * 1nat == x % z);
    } else {
        mod_exp_helper(x, (y - 1) as nat, z);
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
        mod_mult_assoc(x, exp_int(x, (y - 1) as nat), z);
    }
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
/* code modified by LLM (iteration 10): fixed assert statement syntax error */
{
    if n == 0 {
        proof {
            assert(y as nat == exp_int(2nat, 0nat));
            assert(y as nat == 1nat);
            assert(exp_int(x as nat, y as nat) == exp_int(x as nat, 1nat));
            exp_int_base_case(x as nat);
            assert(exp_int(x as nat, 1nat) == x as nat);
        }
        (x % z)
    } else {
        let half_y = y / 2;
        let temp = mod_exp_pow2_int(x, half_y, (n - 1), z);
        proof {
            assert(half_y as nat == exp_int(2nat, (n - 1) as nat));
            assert(y as nat == exp_int(2nat, n as nat));
            assert(y as nat == 2nat * half_y as nat);
            exp_int_mult(x as nat, half_y as nat, half_y as nat);
            assert(exp_int(x as nat, y as nat) == exp_int(x as nat, half_y as nat) * exp_int(x as nat, half_y as nat));
            assert(temp as nat == exp_int(x as nat, half_y as nat) % (z as nat));
            mod_mult_assoc(exp_int(x as nat, half_y as nat), exp_int(x as nat, half_y as nat), z as nat);
            assert((exp_int(x as nat, half_y as nat) * exp_int(x as nat, half_y as nat)) % (z as nat) == ((exp_int(x as nat, half_y as nat) % (z as nat)) * (exp_int(x as nat, half_y as nat) % (z as nat))) % (z as nat));
            assert(((exp_int(x as nat, half_y as nat) % (z as nat)) * (exp_int(x as nat, half_y as nat) % (z as nat))) % (z as nat) == (temp as nat * temp as nat) % (z as nat));
            assert((temp as nat * temp as nat) % (z as nat) == exp_int(x as nat, y as nat) % (z as nat));
            assert(temp < z);
            assert(temp as nat * temp as nat < (z as nat) * (z as nat));
            assert(z <= 255);
            assert((z as nat) * (z as nat) <= 255 * 255);
            assert(255 * 255 == 65025);
            assert(65025 < 65536);
            assert(temp as u16 * temp as u16 < 65536);
        }
        let result = (temp as u16 * temp as u16) % (z as u16);
        assert(result < z as u16);
        assert(result <= 255);
        result as u8
    }
}
// </vc-code>


}

fn main() {}