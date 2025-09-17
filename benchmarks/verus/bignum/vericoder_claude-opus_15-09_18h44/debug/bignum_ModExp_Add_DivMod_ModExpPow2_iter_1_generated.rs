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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == (if y == 0 { 1 % z } else if y % 2 == 0 { (Exp_int(x, y/2) * Exp_int(x, y/2)) % z } else { (x * Exp_int(x, y-1)) % z })
    decreases y
{
    if y == 0 {
    } else if y % 2 == 0 {
        lemma_exp_split(x, y/2, z);
        assert(Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2));
    } else {
        lemma_exp_split(x, y-1, z);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy@.len() == 1 && sy@[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let n = (sy@.len() - 1) as int;
    let mut sy_pow2 = Vec::<char>::new();
    for i in 0..n {
        sy_pow2.push('0');
    }
    sy_pow2.push('1');
    
    let (sy_div, sy_mod) = DivMod(sy, &sy_pow2);
    
    if sy_mod@.len() == 1 && sy_mod@[0] == '0' {
        let half_res = ModExpPow2(sx, &sy_div, n - 1, sz);
        let squared = DivMod(&Add(&half_res, &half_res), sz).1;
        return squared;
    } else {
        let pow_res = ModExpPow2(sx, &sy_pow2, n, sz);
        let rec_res = ModExp(sx, &sy_div, sz);
        let combined = DivMod(&Add(&pow_res, &rec_res), sz).1;
        return combined;
    }
}
// </vc-code>

fn main() {}
}
