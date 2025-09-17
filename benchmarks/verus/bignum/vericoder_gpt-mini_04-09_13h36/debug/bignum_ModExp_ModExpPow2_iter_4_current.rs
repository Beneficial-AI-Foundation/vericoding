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
        if e % 2 == 1 {
            let q = e / 2;
            fn helper(b: nat, r: nat)
                ensures Exp_int(b, 2 * r) == Exp_int(b * b, r)
                decreases r
            {
                if r == 0 {
                } else {
                    helper(b, r - 1);
                }
            }
            helper(base, q);
        } else {
            let q = e / 2;
            fn helper2(b: nat, r: nat)
                ensures Exp_int(b, 2 * r) == Exp_int(b * b, r)
                decreases r
            {
                if r == 0 {
                } else {
                    helper2(b, r - 1);
                }
            }
            helper2(base, q);
        }
    }
}

proof fn mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    let qa = a / m;
    let ra = a % m;
    assert(a == qa * m + ra);
    let qb = b / m;
    let rb = b % m;
    assert(b == qb * m + rb);
    assert(a * b == (qa * m + ra) * (qb * m + rb));
    let k = qa * qb * m + qa * rb + qb * ra;
    assert((qa * m + ra) * (qb * m + rb) == k * m + ra * rb);
    assert(a * b == k * m + ra * rb);
    assert((a * b) % m == (ra * rb) % m);
    assert((ra * rb) % m == ((a % m) * (b % m)) % m);
}

proof fn pow_mod_congruence(a: nat, b: nat, m: nat, e: nat)
    requires m > 0
    requires a % m == b % m
    ensures Exp_int(a, e) % m == Exp_int(b, e) % m
    decreases e
{
    if e == 0 {
        // both sides equal 1 % m
        assert(Exp_int(a, 0) % m == Exp_int(b, 0) % m);
    } else {
        pow_mod_congruence(a, b, m, e - 1);
        // (a * Exp_int(a,e-1)) % m == (b * Exp_int(b,e-1)) % m
        mod_mul(a, Exp_int(a, e - 1), m);
        mod_mul(b, Exp_int(b, e - 1), m);
        assert((a * Exp_int(a, e - 1)) % m == ((a % m) * (Exp_int(a, e - 1) % m)) % m);
        assert((b * Exp_int(b, e - 1)) % m == ((b % m) * (Exp_int(b, e - 1) % m)) % m);
        assert(a % m == b % m);
        assert(Exp_int(a, e - 1) % m == Exp_int(b, e - 1) % m);
        assert(((a % m) * (Exp_int(a, e - 1) % m)) % m == ((b % m) * (Exp_int(b, e - 1) % m)) % m);
        // conclude for exponent e
        assert(Exp_int(a, e) % m == Exp_int(b, e) % m);
    }
}

proof fn IntToSeq_correct(n: nat)
    ensures ValidBitString(IntToSeq(n))
    ensures Str2Int(IntToSeq(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        IntToSeq_correct(n / 2);
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
    // modular exponentiation loop, using binary exponentiation on exp
    while exp > 0
        invariant base < m
        invariant res_nat < m
        invariant (res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m
    {
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
    // convert res_nat to Vec<char> using IntToSeq
    let v = nat_to_vec_via_inttoseq(res_nat);
    return v;
}
// </vc-code>

fn main() {}
}