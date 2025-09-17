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
exec fn vec_to_nat(s: &[char]) -> nat
  ensures result == Str2Int(s@)
{
    let n: int = s.len() as int;
    let mut i: int = 0;
    let mut acc: nat = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant acc == Str2Int(s@.subrange(0, i));
        decreases n - i;
    {
        let ch = s[i as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let old_acc = acc;
        // update acc = 2 * old_acc + bit
        acc = old_acc * 2 + bit;
        // prove the invariant for i+1
        {
            assert(old_acc == Str2Int(s@.subrange(0, i)));
            assert(acc == Str2Int(s@.subrange(0, i + 1)));
        }
        i += 1;
    }
    acc
}

exec fn pow_naive(a: nat, e: nat) -> nat
  ensures result == Exp_int(a, e)
{
    let mut e0: nat = e;
    let mut res: nat = 1;
    // invariant: res * Exp_int(a, e) == Exp_int(a, e0)
    while e > 0
        invariant res * Exp_int(a, e) == Exp_int(a, e0);
        invariant e <= e0;
        decreases e;
    {
        let old_res = res;
        let old_e = e;
        assert(old_e > 0);
        assert(a * Exp_int(a, old_e - 1) == Exp_int(a, old_e));
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
        // update
        pow = old_pow * 2;
        k = old_k + 1;
        // prove pow == Exp_int(2, k)
        assert(old_pow == Exp_int(2, old_k));
        assert(2 * Exp_int(
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
exec fn vec_to_nat(s: &[char]) -> nat
  ensures result == Str2Int(s@)
{
    let n: int = s.len() as int;
    let mut i: int = 0;
    let mut acc: nat = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant acc == Str2Int(s@.subrange(0, i));
        decreases n - i;
    {
        let ch = s[i as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let old_acc = acc;
        // update acc = 2 * old_acc + bit
        acc = old_acc * 2 + bit;
        // prove the invariant for i+1
        {
            assert(old_acc == Str2Int(s@.subrange(0, i)));
            assert(acc == Str2Int(s@.subrange(0, i + 1)));
        }
        i += 1;
    }
    acc
}

exec fn pow_naive(a: nat, e: nat) -> nat
  ensures result == Exp_int(a, e)
{
    let mut e0: nat = e;
    let mut res: nat = 1;
    // invariant: res * Exp_int(a, e) == Exp_int(a, e0)
    while e > 0
        invariant res * Exp_int(a, e) == Exp_int(a, e0);
        invariant e <= e0;
        decreases e;
    {
        let old_res = res;
        let old_e = e;
        assert(old_e > 0);
        assert(a * Exp_int(a, old_e - 1) == Exp_int(a, old_e));
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
        // update
        pow = old_pow * 2;
        k = old_k + 1;
        // prove pow == Exp_int(2, k)
        assert(old_pow == Exp_int(2, old_k));
        assert(2 * Exp_int(
// </vc-code>

fn main() {}
}