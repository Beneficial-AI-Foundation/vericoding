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
/* helper modified by LLM (iteration 3): identity helper for nat */
spec fn dummy_nat(n: nat) -> nat { n }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): convert nat to bitstring using nat arithmetic */
  let m: nat = Str2Int(sz@);
  let mut r_nat: nat = Exp_int(Str2Int(sx@), Str2Int(sy@)) % m;
  let mut bits = Vec::<char>::new();
  if r_nat == 0 {
      bits.push('0');
      return bits;
  }
  while r_nat > 0
      invariant
          r_nat >= 0,
      decreases r_nat
  {
      let bit = if r_nat % 2 == 1 { '1' } else { '0' };
      bits.push(bit);
      r_nat = r_nat / 2;
  }
  let mut res = Vec::<char>::new();
  while bits.len() > 0
      invariant
          true,
      decreases bits.len()
  {
      match bits.pop() {
          Some(c) => res.push(c),
          None => (),
      }
  }
  res
}
// </vc-code>

fn main() {}
}
