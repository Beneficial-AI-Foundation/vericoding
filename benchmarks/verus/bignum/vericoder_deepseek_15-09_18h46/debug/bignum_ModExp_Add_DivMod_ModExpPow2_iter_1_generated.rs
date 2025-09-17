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
proof fn lemma_exp_zero(x: nat) ensures Exp_int(x, 0) == 1 { }
proof fn lemma_exp_rec(x: nat, y: nat) requires y > 0 ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat) { }
proof fn lemma_str2int_empty() ensures Str2Int(Seq::<char>::empty()) == 0 { }
proof fn lemma_str2int_rec(s: Seq<char>, c: char) requires ValidBitString(s.push(c)), s.len() > 0 ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }) { }
proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat) requires z > 1 ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z { }
proof fn lemma_mod_exp_pow2_base(x: nat, n: nat, z: nat) requires z > 1 ensures Exp_int(x, Exp_int(2, n)) % z == Exp_int(Exp_int(x, Exp_int(2, n - 1)) % z, 2) % z { }
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
    let n = sy@.len() as int - 1;
    let (mut result, mut base, mut exponent) = (Vec::new(), sx.to_vec(), sy.to_vec());
    
    while exponent.len() > 0
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            ValidBitString(exponent@),
            Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@) - Str2Int(exponent@)) % Str2Int(sz@),
            exponent@.len() <= sy@.len()
        decreases exponent@.len()
    {
        let last_char = *exponent.last().unwrap();
        exponent.pop();
        
        if last_char == '1' {
            let temp = ModExpPow2(base.as_slice(), exponent.as_slice(), n, sz.as_slice());
            result = Add(result.as_slice(), temp.as_slice());
            result = DivMod(result.as_slice(), sz.as_slice()).1;
        }
        
        base = ModExpPow2(base.as_slice(), exponent.as_slice(), n, sz.as_slice());
        base = DivMod(base.as_slice(), sz.as_slice()).1;
        n = n - 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
