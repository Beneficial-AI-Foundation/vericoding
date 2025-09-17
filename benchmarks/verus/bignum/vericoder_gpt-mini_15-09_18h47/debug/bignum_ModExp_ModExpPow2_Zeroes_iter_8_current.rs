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
/* helper modified by LLM (iteration 8): convert nat to bit-sequence (MSB-first) */
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
  /* code modified by LLM (iteration 8): modular exponentiation with bit conversion, assign to named return */

  let mut i: usize = 0;
  let mut x_val: nat = 0;
  while i < sx.len()
      invariant
          i <= sx.len(),
          x_val == Str2Int(sx@.subrange(0, i as int)),
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
  let mut z_val: nat = 0;
  while j < sz.len()
      invariant
          j <= sz.len(),
          z_val == Str2Int(sz@.subrange(0, j as int)),
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
  let mut res_val: nat = 1 % z_val;
  let mut base: nat = x_val % z_val;
  let mut k: usize = 0;
  while k < m
      invariant
          k <= m,
          res_val == Exp_int(x_val, Str2Int(sy@.subrange((m - k) as int, m as int))) % z_val,
          base == Exp_int(x_val, Exp_int(2, k as nat)) % z_val,
      decreases m - k
  {
      let b = sy[(m - 1) - k];
      if b == '1' {
          res_val = (res_val * base) % z_val;
      }
      base = (base * base) % z_val;
      k += 1;
  }

  let tmp_seq = nat_to_bits_seq(res_val);
  let tmp_len: int = tmp_seq.len() as int;
  let mut res: Vec<char> = Vec::new();
  let mut idx: int = 0;
  while idx < tmp_len
      invariant
          0 <= idx && idx <= tmp_len,
      decreases tmp_len - idx
  {
      res.push(tmp_seq.index(idx));
      idx += 1;
  }

  res
}

// </vc-code>

fn main() {}
}
