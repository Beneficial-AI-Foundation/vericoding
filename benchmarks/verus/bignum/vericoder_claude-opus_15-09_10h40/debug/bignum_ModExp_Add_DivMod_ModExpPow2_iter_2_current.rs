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
/* helper modified by LLM (iteration 2): Fixed type errors by using nat instead of int where appropriate */
exec fn find_highest_power_of_2(sy: &[char]) -> (n: nat)
    requires
        ValidBitString(sy@),
        sy@.len() > 0,
        Str2Int(sy@) > 0,
    ensures
        n >= 0,
        Exp_int(2, n) <= Str2Int(sy@),
        Exp_int(2, n + 1) > Str2Int(sy@),
{
    let mut n: nat = 0;
    let mut power: Vec<char> = vec!['1'];
    
    while Str2Int(power@) * 2nat <= Str2Int(sy@)
        invariant
            ValidBitString(power@),
            Str2Int(power@) == Exp_int(2, n),
            Exp_int(2, n) <= Str2Int(sy@),
    {
        power = vec!['0'];
        let mut i: nat = 0;
        while i <= n
            invariant
                0 <= i <= n + 1,
                ValidBitString(power@),
                power@.len() == i + 1,
        {
            power.push('0');
            i = i + 1;
        }
        n = n + 1;
    }
    
    return n;
}

exec fn create_power_of_2(n: nat) -> (res: Vec<char>)
    requires
        n >= 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Exp_int(2, n),
        res@.len() == n + 1,
{
    let mut res = vec!['1'];
    let mut i: nat = 0;
    while i < n
        invariant
            0 <= i <= n,
            ValidBitString(res@),
            res@.len() == i + 1,
            Str2Int(res@) == Exp_int(2, i),
    {
        res.push('0');
        i = i + 1;
    }
    return res;
}

exec fn subtract_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        Str2Int(s1@) >= Str2Int(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@),
{
    // Using DivMod to compute s1 - s2 by finding quotient and remainder of (s1 + (max - s2)) / max
    // where max is a large enough power of 2
    let mut max_bits = vec!['1'];
    let mut i: nat = 0;
    while i < s1@.len() + 1
        invariant
            0 <= i <= s1@.len() + 1,
            ValidBitString(max_bits@),
            max_bits@.len() == i + 1,
    {
        max_bits.push('0');
        i = i + 1;
    }
    
    // max_bits now represents 2^(s1.len + 2), which is larger than s1
    let (q1, r1) = DivMod(&max_bits, s2);
    let complement = r1;
    
    // s1 - s2 = (s1 + complement) mod max
    let sum = Add(s1, &complement);
    let (q2, r2) = DivMod(&sum, &max_bits);
    
    return r2;
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
/* code modified by LLM (iteration 2): Fixed type errors by using nat and proper indexing */
{
    if sy@.len() == 1nat && sy[0] == '0' {
        return vec!['1'];
    }
    
    let n = find_highest_power_of_2(sy);
    let power_of_2 = create_power_of_2(n);
    let remainder = subtract_bit_strings(sy, &power_of_2);
    
    let x_to_power = ModExpPow2(sx, &power_of_2, n as int, sz);
    
    if remainder@.len() == 0 || (remainder@.len() == 1 && remainder[0] == '0') {
        return x_to_power;
    }
    
    let x_to_remainder = ModExp(sx, &remainder, sz);
    let product = Add(&x_to_power, &x_to_remainder);
    let (q, r) = DivMod(&product, sz);
    
    return r;
}
// </vc-code>

fn main() {}
}
