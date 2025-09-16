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
/* code modified by LLM (iteration 3): fixed type mismatches in Nat2Str by casting to nat */
    fn Nat2Str(n: nat) -> Vec<char> decreases n {
      if n == 0nat { Vec::new() } else { let mut s = Nat2Str((n / 2) as nat); s.push(if n % 2 == 0nat { '0' } else { '1' }); s }
    }
    
    let a = Str2Int(s1@);
    let b = Str2Int(s2@);
    Nat2Str(a + b)
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatches in Nat2Str by casting to nat */
    fn Nat2Str(n: nat) -> Vec<char> decreases n {
      if n == 0nat { Vec::new() } else { let mut s = Nat2Str((n / 2) as nat); s.push(if n % 2 == 0nat { '0' } else { '1' }); s }
    }
    
    let a = Str2Int(dividend@);
    let b = Str2Int(divisor@);
    let quot = Nat2Str(a / b);
    let rem = Nat2Str(a % b);
    (quot, rem)
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatches in Nat2Str by casting to nat */
    fn Nat2Str(n: nat) -> Vec<char> decreases n {
      if n == 0nat { Vec::new() } else { let mut s = Nat2Str((n / 2) as nat); s.push(if n % 2 == 0nat { '0' } else { '1' }); s }
    }
    
    let a = Str2Int(s1@);
    let b = Str2Int(s2@);
    Nat2Str(a * b)
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatches in Nat2Str and result initialization by casting to nat */
    fn Nat2Str(n: nat) -> Vec<char> decreases n {
      if n == 0nat { Vec::new() } else { let mut s = Nat2Str((n / 2) as nat); s.push(if n % 2 == 0nat { '0' } else { '1' }); s }
    }
    
    let mut result: nat = 1nat;
    let mut base: nat = Str2Int(sx@) % Str2Int(sz@);
    let mut i: usize = 0;
    let y_len = sy.len();
    while i < y_len {
      invariant
        result >= 1,
        base >= 0,
        i <= y_len,
      decreases (y_len - i)
      if sy[y_len - 1 - i] == '1' {
        result = (result * base) % Str2Int(sz@);
      }
      base = (base * base) % Str2Int(sz@);
      i += 1;
    }
    Nat2Str(result)
// </vc-code>

fn main() {}
}
