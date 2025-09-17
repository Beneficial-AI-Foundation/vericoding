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
        let mut q = nat_to_vec_bits(n / 2);
        if n % 2 == 1 {
            q.push('1');
        } else {
            q.push('0');
        }
        proof {
            let d = n / 2;
            let r = n % 2;
            assert(n == 2 * d + r);
            assert(Str2Int(q@) == d);
            if r == 1 {
                assert(q.index((q.len() as int) - 1) == '1');
            } else {
                assert(q.index((q.len() as int) - 1) == '0');
            }
            // From definition of Str2Int on sequences:
            // Str2Int(q@) == 2 * Str2Int(prefix) + lastbit == 2*d + r == n
            // We can conclude Str2Int(q@) == n by unfolding the definition
        }
        q
    }
}

proof fn lemma_exp_add(x: nat, i: nat, j: nat)
  decreases j
{
    if j == 0 {
    } else {
        lemma_exp_add(x, i, j - 1);
    }
}

proof fn lemma_exp_mul(a: nat, b: nat, k: nat)
  decreases k
{
    if k == 0 {
    } else {
        lemma_exp_mul(a, b, k - 1);
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
            // e is odd: e = e-1 + 1
            let s = pow_mod(a, e - 1, m);
            let a_mod = a % m;
            let res = (a_mod * s) % m;
            proof {
                // By IH: s == Exp_int(a, e-1) % m
                let t = Exp_int(a, e - 1);
                assert(s == t % m);
                // Exp_int(a, e) = a * Exp_int(a, e-1)
                assert(Exp_int(a, e) == a * t);
                // By lemma_mod_mul: (a * t) % m == ((a % m) * (t % m)) % m
                lemma_mod_mul(a, t, m);
                assert((a * t) % m == ((a % m) * (t % m)) % m);
                // RHS equals ((a % m) * s) % m since s == t % m
                assert(((a % m) * (t % m)) % m == ((a % m) * s) % m);
                // res = (a_mod * s) % m equals that value
                assert(res == (a * t) % m);
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