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
exec fn StrToNat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = s.subslice(0, s.len() - 1);
        let prefix_val = StrToNat(prefix);
        let last_bit_val = if s[s.len() - 1] == '1' { 1 } else { 0 };
        2 * prefix_val + last_bit_val
    }
}

exec fn NatToStr(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut higher_bits = NatToStr(n / 2);
        if n % 2 == 1 {
            higher_bits.push('1');
        } else {
            higher_bits.push('0');
        }
        higher_bits
    }
}

exec fn ModMul(sa: &[char], sb: &[char], sz: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(sa@),
        ValidBitString(sb@),
        ValidBitString(sz@),
        Str2Int(sz@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(sa@) * Str2Int(sb@)) % Str2Int(sz@),
{
    let a = StrToNat(sa);
    let b = StrToNat(sb);
    let z = StrToNat(sz);
    let prod = a * b;
    let res_nat = prod % z;
    NatToStr(res_nat)
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
    if sy.len() == 0 {
        let mut v = Vec::new();
        v.push('1');
        return v;
    }

    let sy_prefix = sy.subslice(0, sy.len() - 1);
    let last_char = sy[sy.len() - 1];

    let tmp_v = ModExp_DivMod_Mul_Zeroes(sx, &sy_prefix, sz);
    let sq_v = ModMul(&tmp_v, &tmp_v, sz);

    if last_char == '1' {
        ModMul(&sq_v, sx, sz)
    } else {
        sq_v
    }
}
// </vc-code>

fn main() {}
}
