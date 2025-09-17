use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed to_binary helper with correct syntax */
exec fn to_binary(n: nat) -> Vec<char>
    decreases n
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut r = to_binary(n / 2);
        r.push(if n % 2 == 1 { '1' } else { '0' });
        r
    }
}

/* helper modified by LLM (iteration 3): spec function for binary exponentiation */
spec fn bin_exp(base_: nat, e_bits: Seq<char>, m: nat) -> nat
    decreases e_bits.len()
    requires ValidBitString(e_bits), m > 1
{
    if e_bits.len() == 0 {
        1 % m
    } else {
        let last = e_bits.index(e_bits.len() as int - 1);
        let last_bit = if last == '1' { 1 } else { 0 };
        let sub = e_bits.subrange(0, e_bits.len() as int - 1);
        let rec = bin_exp(base_, sub, m);
        let p2 = (rec * rec) % m;
        if last_bit == 1 {
            (p2 * (base_ % m)) % m
        } else {
            p2
        }
    }
}

/* helper modified by LLM (iteration 3): proof of correctness for bin_exp */
proof fn bin_exp_correct(base_: nat, e_bits: Seq<char>, m: nat)
    requires ValidBitString(e_bits), m > 1
    ensures bin_exp(base_, e_bits, m) == Exp_int(base_, Str2Int(e_bits)) % m
    decreases e_bits.len()
{
    if e_bits.len() == 0 {
        assert(Str2Int(e_bits) == 0);
        assert(Exp_int(base_, 0) == 1);
    } else {
        let last = e_bits.index(e_bits.len() as int - 1);
        let is_one = last == '1';
        let sub = e_bits.subrange(0, e_bits.len() as int - 1);
        let sub_val = Str2Int(sub);
        let e_val = Str2Int(e_bits);
        assert(if is_one { e_val == 2 * sub_val + 1 } else { e_val == 2 * sub_val });
        bin_exp_correct(base_, sub, m);
        assert(bin_exp(base_, sub, m) == Exp_int(base_, sub_val) % m);
        let exp_base_sub = Exp_int(base_, sub_val);
        if is_one {
            assert(Exp_int(base_, e_val) == exp_base_sub * exp_base_sub * base_);
        } else {
            assert(Exp_int(base_, e_val) == exp_base_sub * exp_base_sub);
        }
        proof {
            let r1 = bin_exp(base_, sub, m);
            let r2 = r1;
            let bm = base_ % m;
            let r12 = (r1 * r2) % m;
            let rec = Exp_int(base_, sub_val);
            assert((rec % m * rec % m) % m == (rec * rec) % m);
            if is_one {
                let p2_b = (r12 * bm) % m;
                assert(Exp_int(base_, e_val) % m == (exp_base_sub * exp_base_sub * base_) % m);
                assert(r12 == (exp_base_sub * exp_base_sub) % m);
                assert((exp_base_sub * exp_base_sub * base_) % m == ((exp_base_sub * exp_base_sub) % m * bm) % m);
            } else {
                assert(Exp_int(base_, e_val) % m == (exp_base_sub * exp_base_sub) % m);
            }
        }
    }
}

/* helper modified by LLM (iteration 3): lemma for modular multiplication */
proof fn mod_mul_t(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a % m * b % m) % m == (a * b) % m
{
    let am = a % m;
    let bm = b % m;
    assert(am * bm == (a * b) % m);
}

/* helper modified by LLM (iteration 3): executable function for modular exponentiation */
exec fn mod_exp(base_: nat, e_bits: Seq<char>, m: nat) -> nat
    requires ValidBitString(e_bits), m > 1
    ensures result == Exp_int(base_, Str2Int(e_bits)) % m
    decreases e_bits.len()
{
    if e_bits.len() == 0 {
        1 % m
    } else {
        let last = e_bits.index(e_bits.len() as int - 1);
        let last_bit = if last == '1' { 1 } else { 0 };
        let sub = e_bits.subrange(0, e_bits.len() as int - 1);
        let rec = mod_exp(base_, sub, m);
        let p2 = (rec * rec) % m;
        if last_bit == 1 {
            (p2 * (base_ % m)) % m
        } else {
            p2
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): implements the function using binary exponentiation */
    let mod_val = Str2Int(sz@);
    let base_val = Str2Int(sx@);
    let exp_str = sy@;
    let result_num = mod_exp(base_val, exp_str, mod_val);
    let result_vec = to_binary(result_num);
    result_vec
}
// </vc-code>

fn main() {}
}
