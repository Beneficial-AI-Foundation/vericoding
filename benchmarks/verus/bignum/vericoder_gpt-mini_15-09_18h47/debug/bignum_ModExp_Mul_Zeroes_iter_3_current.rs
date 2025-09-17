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
/* helper modified by LLM (iteration 3): lemma that Str2Int yields non-negative nat */
proof fn str2int_nonneg(s: Seq<char>) ensures Str2Int(s) >= 0 { }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute nat values via spec Str2Int, binary exponentiation by scanning exponent bits, and convert result to Vec<char> */
  let modulus: nat = Str2Int(sz@);
  let base: nat = Str2Int(sx@) % modulus;
  let exp_len: int = sy@.len() as int;
  let mut res_int: nat = 1 % modulus;
  let mut i: int = 0;
  while i < exp_len
      invariant
          0 <= i, i <= exp_len,
      decreases exp_len - i
  {
      let bit = sy@.index(i);
      res_int = (res_int * res_int) % modulus;
      if bit == '1' {
          res_int = (res_int * base) % modulus;
      }
      i += 1;
  }

  let mut resv = Vec::<char>::new();
  if res_int == 0 {
      return resv;
  }
  let mut val: nat = res_int;
  while val > 0
      invariant
          val >= 0,
      decreases val
  {
      let b = if val % 2 == 1 { '1' } else { '0' };
      resv.insert(0, b);
      val = val / 2;
  }

  resv
}
// </vc-code>

fn main() {}
}
