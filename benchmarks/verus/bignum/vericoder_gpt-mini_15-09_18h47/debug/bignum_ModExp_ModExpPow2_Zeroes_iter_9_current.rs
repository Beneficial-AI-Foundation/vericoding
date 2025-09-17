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
/* helper modified by LLM (iteration 9): convert nat to bit-sequence (MSB-first) */
spec fn nat_to_bits_seq(n: nat) -> Seq<char>
    ensures
        ValidBitString(result),
        Str2Int(result) == n,
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        nat_to_bits_seq(q) + seq![if r == 1 { '1' } else { '0' }]
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): modular exponentiation using runtime usize arithmetic, return binary Vec<char> */

  let mut i: usize = 0;
  let mut x_val: usize = 0;
  while i < sx.len()
      invariant
          i <= sx.len(),
      decreases sx.len() - i
  {
      let c = sx[i];
      if c == '1' {
          x_val = 2 * x_val + 1;
      } else {
          x_val = 2 * x_val;
      }
      i += 1;
  }

  let mut j: usize = 0;
  let mut z_val: usize = 0;
  while j < sz.len()
      invariant
          j <= sz.len(),
      decreases sz.len() - j
  {
      let c = sz[j];
      if c == '1' {
          z_val = 2 * z_val + 1;
      } else {
          z_val = 2 * z_val;
      }
      j += 1;
  }

  let m: usize = sy.len();
  let mut res_val: usize = if z_val == 0 { 0 } else { 1 % z_val };
  let mut base: usize = if z_val == 0 { 0 } else { x_val % z_val };
  let mut k: usize = 0;
  while k < m
      invariant
          k <= m,
      decreases m - k
  {
      let b = sy[(m - 1) - k];
      if b == '1' {
          if z_val != 0 {
              res_val = (res_val * base) % z_val;
          }
      }
      if z_val != 0 {
          base = (base * base) % z_val;
      }
      k += 1;
  }

  let mut res: Vec<char> = Vec::new();
  if res_val == 0 {
      res.push('0');
  } else {
      let mut tmp = res_val;
      let mut bits: Vec<char> = Vec::new();
      while tmp > 0
          invariant
              tmp >= 0,
          decreases tmp
      {
          let bit = if tmp % 2 == 1 { '1' } else { '0' };
          bits.push(bit);
          tmp = tmp / 2;
      }
      let mut r_idx: usize = 0;
      while r_idx < bits.len()
          invariant
              r_idx <= bits.len(),
          decreases bits.len() - r_idx
      {
          res.push(bits[bits.len() - 1 - r_idx]);
          r_idx += 1;
      }
  }

  res
}

// </vc-code>

fn main() {}
}
