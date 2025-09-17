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
proof fn exp_double(b: nat, r: nat)
    ensures Exp_int(b, 2 * r) == Exp_int(b * b, r)
    decreases r
{
    if r == 0 {
    } else {
        exp_double(b, r - 1);
    }
}

proof fn exp_decompose(base: nat, e: nat)
    ensures if e == 0 {
        Exp_int(base, e) == 1
    } else if e % 2 == 1 {
        Exp_int(base, e) == base * Exp_int(base * base, e / 2)
    } else {
        Exp_int(base, e) == Exp_int(base * base, e / 2)
    }
    decreases e
{
    if e == 0 {
    } else {
        let q = e / 2;
        if e % 2 == 1 {
            // odd: e = 2*q + 1
            proof {
                // Exp_int(base, e) = base * Exp_int(base, e - 1)
                assert(Exp_int(base, e) == base * Exp_int(base, e - 1));
                // e - 1 == 2*q
                assert(e - 1 == 2 * q);
                // use exp_double to relate Exp_int(base, 2*q) and Exp_int(base*base, q)
                exp_double(base, q);
                assert(Exp_int(base, e - 1) == Exp_int(base * base, q));
                assert(base * Exp_int(base, e - 1) == base * Exp_int(base * base, q));
            }
        } else {
            // even: e = 2*q
            proof {
                // e == 2*q
                assert(e == 2 * q);
                // use exp_double to relate Exp_int(base, 2*q) and Exp_int(base*base, q)
                exp_double(base, q);
                assert(Exp_int(base, e) == Exp_int(base * base, q));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // compute numeric values of sx, sy, sz
    let nx = seq_to_nat(sx);
    let mut exp = seq_to_nat(sy);
    let m = seq_to_nat(sz);
    // modulus > 1 is given by precondition
    // reduce base modulo m
    let mut base = nx % m;
    let mut res_nat = 1 % m;
    let orig_a = nx;
    let orig_e = exp;

    // establish loop invariants initially
    proof {
        // m > 0 follows from precondition (m > 1)
        assert(m > 0);
        // base == nx % m by assignment
        assert(base == nx % m);
        // res_nat == 1 % m
        assert(res_nat == 1 % m);
        // base < m and res_nat < m follow from properties of % with m > 0
        assert(base < m);
        assert(res_nat < m);
        // relate Exp_int(nx, orig_e) and Exp_int(base, orig_e) modulo m
        pow_mod_congruence(nx, base, m, orig_e);
        // now show (res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m
        // (1 % m * Exp_int(base, orig_e)) % m == Exp_int(base, orig_e) % m
        mod_mul(1 % m, Exp_int(base, orig_e), m);
        assert((res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m);
    }

    // modular exponentiation loop, using binary exponentiation on exp
    while exp > 0
    {
        invariant base < m;
        invariant res_nat < m;
        invariant (res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m;
        decreases exp;
        if exp % 2 == 1 {
            // odd case: exp = 2*q + 1
            let q = exp / 2;
            // record old values for proof
            let old_res = res_nat;
            let old_base = base;
            let old_exp = exp;
            // update res
            res_nat = (res_nat * base) % m;
            // update base and exp
            base = (old_base * old_base) % m;
            exp = q;
            // proof that invariant is preserved
            proof {
                // ensure m > 0 for using mod_mul and pow_mod_congruence
                assert(m > 0);
                // use invariant before the step
                assert((old_res * Exp_int(old_base, old_exp)) % m == Exp_int(orig_a, orig_e) % m);
                // decompose the exponentiation of old_base
                exp_decompose(old_base, old_exp);
                let qq = q;
                // from decomposition: Exp_int(old_base, old_exp) == old_base * Exp_int(old_base*old_base, qq)
                assert(Exp_int(old_base, old_exp) == old_base * Exp_int(old_base * old_base, qq));
                // rewrite old_res * Exp_int(old_base, old_exp) as (old_res * old_base) * Exp_int(old_base*old_base, qq)
                assert(old_res * Exp_int(old_base, old_exp) == (old_res * old_base) * Exp_int(old_base * old_base, qq));
                // Take mod of both sides: ((old_res * old_base) * Exp_oldsq_qq) % m == (old_res * Exp_int(old_base, old_exp)) % m
                mod_mul(old_res * old_base, Exp_int(old_base * old_base, qq), m);
                assert(((old_res * old_base) * Exp_int(old_base * old_base, qq)) % m == (((old_res * old_base) % m) * (Exp_int(old_base * old_base, qq) % m)) % m);
                // base is (old_base*old_base) % m by assignment above
                assert((old_base * old_base) % m == base % m);
                // relate Exp_int(old_base*old_base, qq) and Exp_int(base, qq) modulo m
                pow_mod_congruence(old_base * old_base, base, m, qq);
                // replace Exp_oldsq_qq % m with Exp_base_qq % m
                assert(((old_res * old_base) % m) * (Exp_int(old_base * old_base, qq) % m) % m == ((old_res * old_base) % m) * (Exp_int(base, qq) % m) % m);
                // use mod_mul to move from ((old_res*old_base)%m * Exp_int(base,qq)%m)%m to ((old_res*old_base) * Exp_int(base,qq))%m
                mod_mul(old_res * old_base, Exp_int(base, qq), m);
                assert(((old_res * old_base) % m) * (Exp_int(base, qq) % m) % m == ((old_res * old_base) * Exp_int(base, qq)) % m);
                // combine equalities to conclude:
                // ((old_res * old_base) * Exp_oldsq_qq) % m == ((old_res * old_base) * Exp_base_qq) % m
                // res_nat == (old_res * old_base) % m, exp == qq, base == base
                assert(res_nat == (old_res * old_base) % m);
                // therefore (res_nat * Exp_int(base, exp)) % m == (old_res * Exp_int(old_base, old_exp)) % m
                assert((res_nat * Exp_int(base, exp)) % m == (old_res * Exp_int(old_base, old_exp)) % m);
            }
        } else {
            // even case: exp = 2*q
            let q = exp / 2;
            // record old values for proof
            let old_res = res_nat;
            let old_base = base;
            let old_exp = exp;
            // update base and exp
            base = (old_base * old_base) % m;
            exp = q;
            // res_nat unchanged
            proof {
                assert(m > 0);
                assert((old_res * Exp_int(old_base, old_exp)) % m == Exp_int(orig_a, orig_e) % m);
                exp_decompose(old_base, old_exp);
                let qq = q;
                // from decomposition: Exp_int(old_base, old_exp) == Exp_int(old_base*old_base, qq)
                assert(Exp_int(old_base, old_exp) == Exp_int(old_base * old_base, qq));
                // mod both sides with multiplier old_res
                mod_mul(old_res, Exp_int(old_base * old_base, qq), m);
                assert((old_res * Exp_int(old_base * old_base, qq)) % m == ((old_res % m) * (Exp_int(old_base * old_base, qq) % m)) % m);
                assert((old_res * Exp_int(old_base, old_exp)) % m == (old_res * Exp_int(old_base * old_base, qq)) % m);
                // relate Exp_int(old_base*old_base, qq) and Exp_int(base, qq) modulo m
                assert((old_base * old_base) % m == base % m);
                pow_mod_congruence(old_base * old_base, base, m, qq);
                // now replace and conclude
                mod_mul(old_res, Exp_int(base, qq), m);
                assert((old_res * Exp_int(base, qq)) % m == ((old_res % m) * (Exp_int(base, qq) % m)) % m);
                // old_res < m because of invariant, so old_res % m == old_res
                assert(old_res % m == old_res);
                assert((old_res * Exp_int(base, qq)) % m == (old_res * Exp_int(old_base, old_exp)) % m);
                // since res_nat == old_res and exp == qq, invariant holds
                assert(res_nat == old_res);
                assert((res_nat * Exp_int(base, exp)) % m == (old_res * Exp_int(old_base, old_exp)) % m);
            }
        }
    }
    // at loop exit exp == 0, establish final equality
    proof {
        assert(exp == 0);
        assert((res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m);
        assert(Exp_int(base, 0) == 1);
        assert((res_nat * 1) % m == Exp_int(orig_a, orig_e) % m);
        assert(res_nat % m == Exp_int(orig_a, orig_e) % m);
        // res_nat < m, so res_nat % m == res_nat
        assert(res_nat < m);
        assert(res_nat == Exp_int(orig_a, orig_e) % m);
    }
    // convert res_nat to Vec<char> using IntToSeq
    let v = nat_to_vec_via_inttoseq(res_nat);
    return v;
}
// </vc-code>

fn main() {}
}