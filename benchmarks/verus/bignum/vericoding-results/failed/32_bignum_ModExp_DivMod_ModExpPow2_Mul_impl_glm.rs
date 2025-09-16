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
exec fn str_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut res = 0;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant res == Str2Int(s@.subrange(0, i))
        decreases s.len() - i
    {
        if s[i] == '1' {
            res = res * 2 + 1;
        } else {
            res = res * 2;
        }
        i = i + 1;
    }
    res
}

exec fn int_to_str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut v = Vec::new();
    let mut current = n;
    while current > 0
        invariant current <= n
        ensures current == 0
        decreases current
    {
        let digit = (current % 2) as int;
        assert(digit == 0 || digit == 1);
        current = current / 2;
        v.push(if digit == 1 { '1' } else { '0' });
    }
    v.reverse();
    v
}

exec fn mod_exp(mut base: nat, mut exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
{
    let mut res = 1;
    base = base % modulus;
    let mut b = base;
    let mut e = exp;
    while e > 0
        invariant
            0 <= res < modulus,
            0 <= b < modulus,
            res * Exp_int(b, e) % modulus == Exp_int(base, exp) % modulus
        decreases e
    {
        if (e % 2) == 1 {
            res = (res * b) % modulus;
        }
        b = (b * b) % modulus;
        e = e / 2;
    }
    res
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
    /* code modified by LLM (iteration 2): fixed implementation using helper functions */
    let base = str_to_int(sx);
    let exp = str_to_int(sy);
    let modulus = str_to_int(sz);
    let res_nat = mod_exp(base, exp, modulus);
    let res = int_to_str(res_nat);
    res
}
// </vc-code>

fn main() {}
}
