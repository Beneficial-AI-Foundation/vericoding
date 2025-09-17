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
/* helper modified by LLM (iteration 5): proof that Str2Int(s) is non-negative */
proof fn str2int_nonneg(s: Seq<char>) ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        str2int_nonneg(s.subrange(0, s.len() as int - 1));
        assert(2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute modular exponentiation with verified loop decreases */
  // parse sz into modulus (MSB at index 0)
  let mut modulus: u128 = 0;
  let mut i: usize = 0;
  while i < sz.len()
      invariant
          i <= sz.len(),
      decreases
          sz.len() - i
  {
      let c = sz[i];
      modulus = modulus * 2 + if c == '1' { 1 } else { 0 };
      i += 1;
  }

  if modulus <= 1 {
      return Vec::<char>::new();
  }

  // parse base
  let mut base: u128 = 0;
  let mut j: usize = 0;
  while j < sx.len()
      invariant
          j <= sx.len(),
      decreases
          sx.len() - j
  {
      let c = sx[j];
      base = base * 2 + if c == '1' { 1 } else { 0 };
      j += 1;
  }
  base = base % modulus;

  // binary exponentiation using exponent bits from LSB (last char) to MSB (first char)
  let mut res_int: u128 = 1 % modulus;
  let mut power: u128 = base;
  let mut k: usize = sy.len();
  while k > 0
      invariant
          k <= sy.len(),
      decreases
          k
  {
      k -= 1;
      let bit = sy[k];
      if bit == '1' {
          res_int = (res_int * power) % modulus;
      }
      power = (power * power) % modulus;
  }

  let mut resv = Vec::<char>::new();
  if res_int == 0 {
      return resv;
  }

  // convert res_int to bits (MSB first)
  let mut bits_rev: Vec<char> = Vec::new();
  let mut val: u128 = res_int;
  let mut count: usize = 0;
  while val > 0
      invariant
          count <= 128,
      decreases
          128 - count
  {
      let b = if (val % 2) == 1 { '1' } else { '0' };
      bits_rev.insert(0, b);
      val = val / 2;
      count += 1;
  }

  resv = bits_rev;
  resv
}
// </vc-code>

fn main() {}
}
