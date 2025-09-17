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
exec fn vec_to_nat_rec(s: &[char], i: int) -> nat
  requires 0 <= i && i <= s.len() as int
  ensures result == Str2Int(s@.subrange(0, i))
  decreases s.len() as int - i
{
    if i == 0 {
        0
    } else {
        let prev = vec_to_nat_rec(s, i - 1);
        let ch = s[(i - 1) as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        prev * 2 + bit
    }
}

exec fn vec_to_nat(s: &[char]) -> nat
  ensures result == Str2Int(s@)
{
    vec_to_nat_rec(s, s.len() as int)
}

exec fn pow_naive(a: nat, e0: nat) -> nat
  ensures result == Exp_int(a, e0)
{
    let mut e: nat = e0;
    let mut res: nat = 1;
    while e > 0
        invariant res * Exp_int(a, e) == Exp_int(a, e0);
        invariant e <= e0;
        decreases e;
    {
        let old_res = res;
        let old_e = e;
        assert(old_e > 0);
        // Exp_int(a, old_e) == a * Exp_int(a, old_e - 1) for old_e > 0
        assert(Exp_int(a, old_e) == a * Exp_int(a, old_e - 1));
        res = old_res * a;
        e = old_e - 1;
        assert(old_res * Exp_int(a, old_e) == Exp_int(a, e0));
        assert(res * Exp_int(a, e) == Exp_int(a, e0));
    }
    res
}

exec fn int_to_vec(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
{
    if n == 0 {
        return Vec::<char>::new();
    }

    // find k such that pow = 2^k > n
    let mut k: nat = 0;
    let mut pow: nat = 1; // 2^0
    while pow <= n
        invariant pow == Exp_int(2, k);
        invariant k <= n + 1;
        decreases (n + 1) - k;
    {
        let old_pow = pow;
        let old_k = k;
        pow = old_pow * 2;
        k = old_k + 1;
        assert(old_pow == Exp_int(2, old_k));
        assert(pow == Exp_int(2, k));
    }

    // build bits from most-significant to least-significant
    let mut v: Vec<char> = Vec::new();
    let mut rem: nat = n;
    let mut i: nat = k;
    let mut p: nat = pow; // p == 2^i
    while i > 0
        invariant p == Exp_int(2, i);
        invariant rem + Str2Int(v@) * Exp_int(2, i) == n;
        invariant ValidBitString(v@);
        decreases i;
    {
        // i > 0 here
        // w = 2^(i-1)
        let w: nat = p / 2;
        // prove w == Exp_int(2, i - 1)
        assert(p == Exp_int(2, i));
        assert(i > 0);
        assert(Exp_int(2, i) == 2 * Exp_int(2, i - 1));
        assert(p == 2 * Exp_int(2, i - 1));
        assert(w == Exp_int(2, i - 1));
        // pick bit for weight w
        if rem >= w {
            rem = rem - w;
            v.push('1');
        } else {
            v.push('0');
        }
        p = w;
        i = i - 1;
        // loop invariants preserved by the above reasoning
    }
    // after loop, i == 0, so Exp_int(2,0)=1 and rem + Str2Int(v@) == n
    assert(Exp_int(2, 0) == 1);
    assert(rem + Str2Int(v@) * 1 == n);
    // rem must be 0 because 0 <= rem < 1 (since pow > n and we extracted all bits), but we can deduce rem == 0
    // however we don't need to assert rem == 0 explicitly; from rem + Str2Int(v@) == n we get Str2Int(v@) == n
    assert(Str2Int(v@) == n);
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a = vec_to_nat(sx);
    let e = vec_to_nat(sy);
    let m = vec_to_nat(sz);
    let p = pow_naive(a, e);
    let r = p % m;
    let res = int_to_vec(r);
    res
}
// </vc-code>

fn main() {}
}