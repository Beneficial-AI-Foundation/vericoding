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
  /* code modified by LLM (iteration 3): fix compilation error by removing 'exec' from helper functions */
  fn to_bin(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
  {
    spec fn num_bits(n: nat) -> nat
    {
      if n == 0 { 0 } else { 1 + num_bits(n / 2) }
    }
    fn build_bits(n: nat, bits: nat) -> Vec<char>
      decreases bits
    {
      if bits == 0 {
        Vec::new()
      } else {
        let rest = build_bits(n / 2, bits - 1);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        if rest.is_empty() {
          vec![bit]
        } else {
          let mut r = rest;
          r.push(bit);
          r
        }
      }
    }
    if n == 0 {
      vec!['0']
    } else {
      build_bits(n, num_bits(n))
    }
  }
  let a = Str2Int(s1@);
  let b = Str2Int(s2@);
  return to_bin(a + b);
}
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
{
  /* code modified by LLM (iteration 3): fix compilation error by removing 'exec' from helper functions */
  fn to_bin(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
  {
    spec fn num_bits(n: nat) -> nat
    {
      if n == 0 { 0 } else { 1 + num_bits(n / 2) }
    }
    fn build_bits(n: nat, bits: nat) -> Vec<char>
      decreases bits
    {
      if bits == 0 {
        Vec::new()
      } else {
        let rest = build_bits(n / 2, bits - 1);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        if rest.is_empty() {
          vec![bit]
        } else {
          let mut r = rest;
          r.push(bit);
          r
        }
      }
    }
    if n == 0 {
      vec!['0']
    } else {
      build_bits(n, num_bits(n))
    }
  }
  fn square(x: nat) -> nat { x * x }
  fn mod_mul(a: nat, b: nat, m: nat) -> nat { (a * b) % m }
  fn mod_pow(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
  {
    if exp == 0 {
      1
    } else if exp % 2 == 1 {
      mod_mul(base, mod_pow(base, exp - 1, modulus), modulus)
    } else {
      let half = mod_pow(base, exp / 2, modulus);
      mod_mul(half, half, modulus)
    }
  }
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);
  let res_num = mod_pow(x, y, z);
  return to_bin(res_num);
}
// </vc-code>

fn main() {}
}


