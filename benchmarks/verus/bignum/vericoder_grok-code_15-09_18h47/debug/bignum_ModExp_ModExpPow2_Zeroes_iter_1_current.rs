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
exec fn str_to_int(s: &[char]) -> (r: nat)
    requires ValidBitString(s@)
    ensures r == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 { 0 } else { (2 * str_to_int(&s[..(s.len() - 1) as usize])) + (if s[(s.len() - 1) as usize] == '1' { 1nat } else { 0nat }) }
}

exec fn mod_exp(base: nat, exp: nat, mod: nat) -> (r: nat)
    requires
        mod > 1,
        exp >= 0
    ensures r == Exp_int(base, exp) % mod
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let half = mod_exp(base, exp / 2, mod);
        let sq = (half * half) % mod;
        if exp % 2 == 1 {
            (sq * base) % mod
        } else {
            sq
        }
    }
}

exec fn nat_to_bin(n: nat) -> (r: Vec<char>)
    ensures
        ValidBitString(r@),
        Str2Int(r@) == n
    decreases n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut tail = nat_to_bin(n / 2);
        if n % 2 == 1 {
            tail.push('1');
        } else {
            tail.push('0');
        }
        tail
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = str_to_int(sx);
    let exp = str_to_int(sy);
    let md = str_to_int(sz);
    let res_nat = mod_exp(base, exp, md);
    let res_vec = nat_to_bin(res_nat);
    res_vec
}
// </vc-code>

fn main() {}
}
