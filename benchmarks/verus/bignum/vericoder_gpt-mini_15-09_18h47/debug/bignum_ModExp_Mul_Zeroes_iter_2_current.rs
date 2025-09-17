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
/* helper modified by LLM (iteration 2): min for usize to avoid nat/int in exec code */
fn min(a: usize, b: usize) -> usize { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced nat/int with usize and implemented parsing, modular exponentiation, conversion */
  // Parse sx into base (binary string MSB..LSB)
  let mut base: usize = 0;
  let mut i: usize = 0;
  while i < sx.len()
      invariant
          i <= sx.len(),
      decreases sx.len() - i
  {
      let c = sx[i];
      base = base * 2 + (if c == '1' { 1 } else { 0 });
      i += 1;
  }

  // Parse sy into exp
  let mut exp: usize = 0;
  i = 0;
  while i < sy.len()
      invariant
          i <= sy.len(),
      decreases sy.len() - i
  {
      let c = sy[i];
      exp = exp * 2 + (if c == '1' { 1 } else { 0 });
      i += 1;
  }

  // Parse sz into modulus
  let mut modulus: usize = 0;
  i = 0;
  while i < sz.len()
      invariant
          i <= sz.len(),
      decreases sz.len() - i
  {
      let c = sz[i];
      modulus = modulus * 2 + (if c == '1' { 1 } else { 0 });
      i += 1;
  }

  // Naive modular exponentiation by repeated multiplication
  let mut res_int: usize = 1 % modulus;
  let mut k: usize = 0;
  while k < exp
      invariant
          k <= exp,
      decreases exp - k
  {
      res_int = (res_int * base) % modulus;
      k += 1;
  }

  // Convert res_int to Vec<char> using MSB..LSB encoding
  let mut resv = Vec::<char>::new();
  if res_int == 0 {
      // empty vector corresponds to 0 by Str2Int spec
      return resv;
  }
  let mut val: usize = res_int;
  while val > 0
      invariant
          val >= 0,
      decreases val
  {
      let bit = if val % 2 == 1 { '1' } else { '0' };
      // insert at front to maintain MSB..LSB order
      resv.insert(0, bit);
      val = val / 2;
  }

  resv
}

// </vc-code>

fn main() {}
}
