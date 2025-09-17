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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let seq1: Seq<char> = s1@;
  let seq2: Seq<char> = s2@;
  let len1 = seq1.len() as int;
  let len2 = seq2.len() as int;
  let max_len = if len1 > len2 { len1 } else { len2 };
  let padded1: Seq<char> = Seq::new(max_len as nat, |i: int| if i < max_len - len1 { '0' } else { seq1@[(i - (max_len - len1)) as int] });
  let padded2: Seq<char> = Seq::new(max_len as nat, |i: int| if i < max_len - len2 { '0' } else { seq2@[(i - (max_len - len2)) as int] });
  let mut carry = 0;
  let mut result: Vec<char> = Vec::new();
  let mut i = 0;
  while i < max_len {
    let pos = max_len - 1 - i;
    let bit1 = padded1@[pos];
    let bit2 = padded2@[pos];
    let b1 = if bit1 == '1' { 1 } else { 0 };
    let b2 = if bit2 == '1' { 1 } else { 0 };
    let sum = b1 + b2 + carry;
    let digit = if sum % 2 == 1 { '1' } else { '0' };
    result.push(digit);
    carry = sum / 2;
    i = i + 1;
  }
  if carry == 1 {
    result.push('1');
  }
  result.reverse();
  return result;
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let seq1 = s1@;
  let seq2 = s2@;
  let len2 = seq2.len() as int;
  let mut acc: Vec<char> = Vec::new();
  acc.push('0');
  let mut i = 0;
  while i < len2 {
    acc.push('0');
    let pos = len2 - 1 - i;
    if seq2@[pos] == '1' {
      let temp = Add(s1, &acc);
      acc = temp;
    }
    i = i + 1;
  }
  return acc;
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  let sn = (sy.len() as int) - 1;
  if sn == 0 {
    if sy[0] == '0' {
      return Vec::<char>::from(['1']);
    } else {
      let num = Str2Int(sx@) % Str2Int(sz@);
      if num == 0 {
        return Vec::from(['0']);
      }
      let mut bits: Vec<char> = Vec::new();
      let mut temp = num;
      while temp > 0 {
        if temp % 2 == 1 { bits.push('1') } else { bits.push('0') };
        temp = temp / 2;
      }
      bits.reverse();
      return bits;
    }
  } else {
    let sy_sub: Vec<char> = Vec::from(y@[1..]);
    let r = ModExpPow2(sx, &sy_sub, sn - 1, sz);
    let m = Mul(&r, &r);
    let den = Str2Int(sz@);
    let mod_res = Str2Int(m@) % den;
    if mod_res == 0 {
      return Vec::from(['0']);
    } else {
      let mut bits: Vec<char> = Vec::new();
      let mut temp = mod_res;
      while temp > 0 {
        if temp % 2 == 1 { bits.push('1') } else { bits.push('0') };
        temp = temp / 2;
      }
      bits.reverse();
      return bits;
    }
  }
}
// </vc-code>

fn main() {}
}
