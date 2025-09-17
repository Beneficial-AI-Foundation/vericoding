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
exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures |res: nat| res == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let pref = &s[..last_idx];
        let v = slice_to_nat(pref);
        if s[last_idx] == '1' { 2 * v + 1 } else { 2 * v }
    }
}

exec fn nat_to_vec_bits(n: nat) -> Vec<char>
  ensures |res: Vec<char>| ValidBitString(res@) && Str2Int(res@) == n
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let d = n / 2;
        let mut q_before = nat_to_vec_bits(d);
        let mut res = q_before.clone();
        let r = n % 2;
        if r == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        proof {
            // n == 2*d + r
            assert(n == 2 * d + r);
            // From recursive call: Str2Int(q_before@) == d
            assert(Str2Int(q_before@) == d);
            // The new vector res is q_before cloned with one bit appended.
            // So prefix of res@ up to len-1 equals q_before@
            assert(res@.subrange(0, res@.len() - 1) == q_before@);
            if r == 1 {
                assert(res@.index(res@.len() - 1) == '1');
            } else {
                assert(res@.index(res@.len() - 1) == '0');
            }
            // By definition of Str2Int on sequences:
            // Str2Int(res@) == 2 * Str2Int(prefix) + lastbit == 2*d + r == n
            assert(Str2Int(res@) == n);
        }
        res
    }
}

proof fn lemma_exp_add(x: nat, i: nat, j: nat)
  decreases j
{
    if j == 0 {
    } else {
        lemma_exp_add(x, i, (j - 1) as nat);
    }
}

proof fn lemma_exp_mul(a: nat, b: nat, k: nat)
  decreases k
{
    if k == 0 {
    } else {
        lemma_exp_mul(a, b, (k - 1) as nat);
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
  requires m > 0
{
    let qa = a / m;
    let ra = a % m;
    let qb = b / m;
    let rb = b % m;
    assert(a == qa * m + ra);
    assert(b == qb * m + rb);
    // a * b = (qa*m + ra) * (qb*m + rb)
    //       = m*(qa*qb*m + qa*rb + ra*qb) + ra*rb
    // therefore (a*b) % m == (ra*rb) % m
    assert((a * b) % m == (ra * rb) % m);
    // also (a % m) == ra and (b % m) == rb, so ((a % m) * (b % m)) % m == (ra*rb) % m
    assert(((a % m) * (b % m)) % m == (ra * rb) % m);
    // conclude
    assert((a * b) % m == ((a % m) * (b % m)) % m);
}

exec fn pow_mod(a: nat, e: nat, m: nat) -> nat
  requires m > 0
  ensures |res: nat| res == Exp_int(a, e) % m
  decreases e
{
    if e == 0 {
        1 % m
    } else {
        if e % 2 == 0 {
            let k = e / 2;
            let r = pow_mod(a, k, m);
            let res = (r * r) % m;
            proof {
                // By IH: r == Exp_int(a,k) % m
                let t = Exp_int(a, k);
                assert(r == t % m);
                // By lemma_mod_mul: (t * t) % m == ((t % m) * (t % m)) % m
                lemma_mod_mul(t, t, m);
                assert((t * t) % m == ((t % m) * (t % m)) % m);
                // res == ((t % m) * (t % m)) % m
                assert(res == ((t % m) * (t % m)) % m);
                // thus res == (t * t) % m
                assert(res == (t * t) % m);
                // t * t == Exp_int(a, 2*k)
                assert(Exp_int(a, 2 * k) == t * t);
                assert(res == Exp_int(a, 2 * k) % m);
                assert(2 * k == e);
            }
            res
        } else {
            // e is odd: e = 2*k + 1
            let k = e / 2;
            let r = pow_mod(a, k, m);
            let rr = (r * r) % m;
            let res = ((a % m) * rr) % m;
            proof {
                // By IH: r == Exp_int(a,k) % m
                let t = Exp_int(a, k);
                assert(r == t % m);
                // rr == (t * t) % m
                lemma_mod_mul(t, t, m);
                assert(rr == ((t % m) * (t % m)) % m);
                assert(rr == (t * t) % m);
                // Exp_int(a, 2*k) == t * t
                assert(Exp_int(a, 2 * k) == t * t);
                // e == 2*k + 1
                assert(2 * k + 1 == e);
                // Exp_int(a, e) == a * Exp_int(a, 2*k)
                assert(Exp_int(a, e) == a * Exp_int(a, 2 * k));
                // (a * (t * t)) % m == ((a % m) * rr) % m
                lemma_mod_mul(a, t * t, m);
                assert((a * (t * t)) % m == ((a % m) * ((t * t) % m)) % m);
                assert(((a % m) * ((t * t) % m)) % m == ((a % m) * rr) % m);
                assert(res == (a * (t * t)) % m);
                assert(res == Exp_int(a, e) % m);
            }
            res
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a = slice_to_nat(sx);
    let e = slice_to_nat(sy);
    let m = slice_to_nat(sz); // m > 1 by precondition
    let r = pow_mod(a, e, m);
    let vec = nat_to_vec_bits(r);
    vec
}
// </vc-code>

fn main() {}
}