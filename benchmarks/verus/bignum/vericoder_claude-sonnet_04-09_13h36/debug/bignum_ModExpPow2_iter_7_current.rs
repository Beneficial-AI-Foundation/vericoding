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
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn IntToStr(x: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == x
{
  if x == 0 {
    let mut result = Vec::new();
    result.push('0');
    result
  } else {
    let mut result = Vec::new();
    let mut val = x;
    while val > 0
      invariant ValidBitString(result@)
    {
      if val % 2 == 0 {
        result.push('0');
      } else {
        result.push('1');
      }
      val = val / 2;
    }
    // Reverse to get correct bit order
    result.reverse();
    result
  }
}

exec fn StrMod(sx: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sz@), Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(sx@) % Str2Int(sz@)
{
  IntToStr(Str2Int(sx@) % Str2Int(sz@))
}

exec fn StrMul(sx: &[char], sy: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(sx@) * Str2Int(sy@)
{
  IntToStr(Str2Int(sx@) * Str2Int(sy@))
}

exec fn IsZero(s: &[char]) -> (res: bool)
  requires ValidBitString(s@)
  ensures res == (Str2Int(s@) == 0)
{
  Str2Int(s@) == 0
}

exec fn IsOne(s: &[char]) -> (res: bool)
  requires ValidBitString(s@)
  ensures res == (Str2Int(s@) == 1)
{
  Str2Int(s@) == 1
}

exec fn DivideByTwo(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@), s@.len() > 0
  ensures ValidBitString(res@), 
    (s@.len() == 1 ==> Str2Int(res@) == 0),
    (s@.len() > 1 ==> Str2Int(res@) * 2 + (if s@[s@.len() as int - 1] == '1' { 1 } else { 0 }) == Str2Int(s@))
{
  if s.len() == 1 {
    let mut result = Vec::new();
    result.push('0');
    result
  } else {
    let mut result = Vec::new();
    for i in 0..(s.len() - 1)
      invariant ValidBitString(result@), result@.len() == i
    {
      result.push(s[i]);
    }
    result
  }
}
// </vc-helpers>

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
  if n == 0 {
    if IsOne(sy) {
      StrMod(sx, sz)
    } else {
      // sy represents 0, so result is 1
      let mut result = Vec::new();
      result.push('1');
      StrMod(&result, sz)
    }
  } else {
    if IsZero(sy) {
      // sy represents 0, so result is 1
      let mut result = Vec::new();
      result.push('1');
      result
    } else {
      // sy represents 2^n, compute x^(2^(n-1)) first
      let sy_half = DivideByTwo(sy);
      let temp = ModExpPow2(sx, &sy_half, n - 1, sz);
      let squared = StrMul(&temp, &temp);
      StrMod(&squared, sz)
    }
  }
}
// </vc-code>

fn main() {}
}