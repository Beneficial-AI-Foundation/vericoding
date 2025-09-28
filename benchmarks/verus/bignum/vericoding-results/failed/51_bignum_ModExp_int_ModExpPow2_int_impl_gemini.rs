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
/* helper modified by LLM (iteration 10): fixed incorrect vstd API paths and function names */
proof fn lemma_mul_mod_right(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == (a * (b % m)) % m
{
    // We want to prove (a*b) % m == (a*(b%m))%m
    // This is equivalent to a*b === a*(b%m) (mod m)
    // We know that b === b%m (mod m)
    // lemma_mul_cong_right says if b1 === b2 (mod m) then a*b1 === a*b2 (mod m)
    // Let b1 = b and b2 = b%m.
    // We need to show b % m == (b%m) % m. This is provided by lemma_mod_basics_auto
    vstd::arithmetic::lemma_mod_basics_auto(b as int, m as int);
    vstd::arithmetic::lemma_mul_cong_right(m as int, a as int, b as int, (b % m) as int);
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
    /* code modified by LLM (iteration 10): fixed incorrect vstd API paths and function names */
    if n == 0 {
        if y == 0 {
            return 1;
        } else { // y == 1
            return x % z;
        }
    }

    let t = mod_exp_int(x, y / 2, (n - 1) as u8, z);

    // widen to 64-bit to prevent overflow on t*t
    let t_w = t as u64;
    let z_w = z as u64;
    let x_w = x as u64;

    let sq = (t_w * t_w) % z_w;

    let res = if y % 2 == 0 {
        sq as u8
    } else {
        ((x_w * sq) % z_w) as u8
    };

    proof {
        let x_nat = x as nat;
        let y_nat = y as nat;
        let z_nat = z as nat;

        let B = exp_int(x_nat, y_nat / 2);
        // prove that sq is correct w.r.t the spec
        // sq in nat is ((t as nat)^2) % z_nat
        // t as nat == exp_int(x_nat, y_nat/2) % z_nat
        // so sq == ((exp_int(x_nat, y_nat/2) % z_nat)^2) % z_nat
        // by lemma_mul_mod_auto, this is equal to exp_int(x_nat, 2*(y_nat/2)) % z_nat
        vstd::arithmetic::lemma_mul_mod_auto(B as int, B as int, z_nat as int);
        
        if y % 2 == 0 {
            assert(y_nat == 2 * (y_nat / 2)) by { vstd::arithmetic::div_mod::lemma_div_auto(y_nat as int, 2); };
        } else {
            assert(y_nat == 2 * (y_nat / 2) + 1) by { vstd::arithmetic::div_mod::lemma_div_auto(y_nat as int, 2); };
            let C = exp_int(x_nat, 2 * (y_nat/2));
            lemma_mul_mod_right(x_nat, C, z_nat);
        }
    }
    res
}
// </vc-code>


}

fn main() {}