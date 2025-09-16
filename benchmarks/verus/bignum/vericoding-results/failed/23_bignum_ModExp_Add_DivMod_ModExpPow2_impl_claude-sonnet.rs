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
/* helper modified by LLM (iteration 10): Removed requires/ensures from spec function log2_floor */
spec fn is_power_of_2(n: nat) -> bool {
    exists |k: nat| n == Exp_int(2, k)
}

spec fn log2_floor(n: nat) -> nat
    decreases n
{
    if n <= 1 { 0 } else { 1 + log2_floor(n / 2) }
}

exec fn find_highest_bit(s: &[char]) -> (pos: usize)
    requires ValidBitString(s@), s@.len() > 0
    ensures pos < s.len()
{
    let mut i = 0;
    while i < s.len() {
        if s[i] == '1' {
            return i;
        }
        i += 1;
    }
    0
}

exec fn is_zero(s: &[char]) -> (result: bool)
    requires ValidBitString(s@)
    ensures result == (Str2Int(s@) == 0)
{
    for i in 0..s.len() {
        if s[i] == '1' {
            return false;
        }
    }
    true
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
    /* code modified by LLM (iteration 10): Fixed type error by using ghost declaration for int value */
    if is_zero(sy) {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let (_, remainder) = DivMod(sx, sz);
        return remainder;
    }
    
    let highest_bit = find_highest_bit(sy);
    let power_len = sy.len() - highest_bit;
    
    if power_len <= 1 {
        let (_, remainder) = DivMod(sx, sz);
        return remainder;
    }
    
    let mut half_exp = Vec::new();
    for i in highest_bit + 1..sy.len() {
        half_exp.push(sy[i]);
    }
    
    let half_result = ModExp(sx, &half_exp, sz);
    let power_len_minus_one = (power_len - 1) as usize;
    
    let ghost ghost_n: int = power_len_minus_one as int;
    
    let squared = ModExpPow2(&half_result, sy, ghost_n, sz);
    
    if sy[highest_bit] == '1' {
        let base_mod = ModExp(sx, &['1'], sz);
        let multiplied = Add(&squared, &base_mod);
        let (_, final_remainder) = DivMod(&multiplied, sz);
        return final_remainder;
    } else {
        return squared;
    }
}
// </vc-code>

fn main() {}
}
