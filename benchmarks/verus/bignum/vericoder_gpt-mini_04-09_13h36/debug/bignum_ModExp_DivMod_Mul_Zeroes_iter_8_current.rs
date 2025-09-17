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
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s@.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let prefix = &s[0..s.len() - 1];
        let p = seq_to_nat(prefix);
        let bit = if s[s.len() - 1] == '1' { 1 } else { 0 };
        return 2 * p + bit;
    }
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
  decreases n
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        proof {
            assert(v@.len() == 0);
            assert(Str2Int(v@) == 0);
            assert(ValidBitString(v@));
        }
        return v;
    } else {
        let mut v = nat_to_bits(n / 2);
        let old = v.clone();
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            let res_seq = v@;
            let old_seq = old@;
            assert(res_seq.len() as int > 0);
            let last_idx: int = res_seq.len() as int - 1;
            assert(res_seq.index(last_idx) == bit);
            assert(res_seq.subrange(0, last_idx) == old_seq);
            assert(Str2Int(old_seq) == n / 2);
            assert(ValidBitString(old_seq));
            assert(Str2Int(res_seq) == 2 * Str2Int(old_seq) + (if bit == '1' { 1 } else { 0 }));
            assert((if bit == '1' { 1 } else { 0 }) == n % 2);
            assert(n == 2 * (n / 2) + n % 2);
            assert(Str2Int(res_seq) == n);
            assert(bit == '0' || bit == '1');
            assert(ValidBitString(res_seq));
        }
        return v;
    }
}

proof fn exp_add(a: nat, e1: nat, e2: nat)
  ensures Exp_int(a, e1 + e2) == Exp_int(a, e1) * Exp_int(a, e2)
  decreases e2
{
    if e2 == 0 {
        // Exp_int(a, e1 + 0) == Exp_int(a, e1) * Exp_int(a, 0) and Exp_int(a,0)==1
        assert(Exp_int(a, e1 + 0) == Exp_int(a, e1));
        assert(Exp_int(a, 0) == 1);
        assert(Exp_int(a, e1 + 0) == Exp_int(a, e1) * Exp_int(a, 0));
    } else {
        // inductive step
        exp_add(a, e1, e2 - 1);
        // Let k = e2 - 1
        let k = e2 - 1;
        // Exp_int(a, e1 + e2) = Exp_int(a, e1 + k + 1) = a * Exp_int(a, e1 + k)
        assert(Exp_int(a, e1 + e2) == a * Exp_int(a, e1 + k));
        // By IH: Exp_int(a, e1 + k) == Exp_int(a, e1) * Exp_int(a, k)
        assert(Exp_int(a, e1 + k) == Exp_int(a, e1) * Exp_int(a, k));
        // combine
        assert(Exp_int(a, e1 + e2) == a * (Exp_int(a, e1) * Exp_int(a, k)));
        // rearrange multiplication
        assert(a * (Exp_int(a, e1) * Exp_int(a, k)) == Exp_int(a, e1) * (a * Exp_int(a, k)));
        // a * Exp_int(a, k) == Exp_int(a, k + 1) == Exp_int(a, e2)
        assert(a * Exp_int(a, k) == Exp_int(a, e2));
        // conclude
        assert(Exp_int(a, e1 + e2) == Exp_int(a, e1) * Exp_int(a, e2));
    }
}

proof fn mul_m_times_mod_zero(k: nat, m: nat)
  ensures (k * m) % m == 0
{
    // trivial by arithmetic decomposition
    assert((k * m) % m == 0);
}

proof fn mul_mod_compat(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
    let aq = a / m;
    let ar = a % m;
    let bq = b / m;
    let br = b % m;
    assert(a == aq * m + ar);
    assert(b == bq * m + br);
    let prod = a * b;
    // prod = (aq*m + ar)*(bq*m + br) = multiple_of_m + ar*br
    // all terms except ar*br are multiples of m
    // show prod % m == (ar * br) % m
    // compute prod - ar*br = m * (aq*bq*m + aq*br + ar*bq)
    assert(prod == (aq * bq) * (m * m) + (aq * br * m) + (ar * bq * m) + (ar * br));
    // therefore prod - ar*br is multiple of m
    assert((prod - ar * br) % m == 0);
    // so prod % m == (ar*br) % m
    assert(prod % m == (ar * br) % m);
    // substitute ar = a % m and br = b % m
    assert(prod % m == ((a % m) * (b % m)) % m);
    assert(((a % m) * (b % m)) % m == (a * b) % m);
}

exec fn pow_mod(a: nat, e: nat, m: nat) -> nat
  requires m > 0
  ensures result == Exp_int(a, e) % m
  decreases e
{
    if e == 0 {
        let r = 1 % m;
        proof {
            assert(Exp_int(a, 0) == 1);
            assert(r == Exp_int(a, e) % m);
        }
        return r;
    } else {
        let t = pow_mod(a, e - 1, m);
        let res = ((a % m) * t) % m;
        proof {
            // t == Exp_int(a, e-1) % m
            assert(t == Exp_int(a, e - 1) % m);
            // relate product mod m
            mul_mod_compat(a, Exp_int(a, e - 1), m);
            assert(((a % m) * (Exp_int(a, e - 1) % m)) % m == (a * Exp_int(a, e - 1)) % m);
            // Exp_int unfolding
            assert(Exp_int(a, e) == a * Exp_int(a, e - 1));
            // conclude
            assert(res == Exp_int(a, e) % m);
        }
        return res;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let m = seq_to_nat(sz);
    proof {
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(m == Str2Int(sz@));
        assert(Str2Int(sz@) > 1);
        assert(m > 0);
    }
    let r = pow_mod(x, y, m);
    let res = nat_to_bits(r);
    proof {
        assert(r == Exp_int(x, y) % m);
        assert(Str2Int(res@) == r);
        // replace x,y,m with Str2Int(sx@), Str2Int(sy@), Str2Int(sz@)
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        assert(ValidBitString(res@));
    }
    return res;
}
// </vc-code>

fn main() {}
}