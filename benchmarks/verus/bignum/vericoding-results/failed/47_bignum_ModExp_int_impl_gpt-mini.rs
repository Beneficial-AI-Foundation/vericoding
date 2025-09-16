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
/* helper modified by LLM (iteration 7): predicate that a character is a binary bit */
spec fn IsBit(c: char) -> bool { c == '0' || c == '1' }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 7): compute modular exponentiation by squaring and convert result to bit vector */
  let m: nat = Str2Int(sz@);
  let mut base: nat = Str2Int(sx@) % m;
  let mut e: nat = Str2Int(sy@);
  let mut result: nat = 1;
  while e > 0
      invariant
          result < m,
          base < m,
      decreases e
  {
      if e % 2 == 1 {
          result = (result * base) % m;
      }
      base = (base * base) % m;
      e = e / 2;
  }
  let mut r_nat: nat = result % m;
  let mut bits = Vec::<char>::new();
  if r_nat == 0 {
      bits.push('0');
  } else {
      while r_nat > 0
          invariant
              r_nat >= 0,
          decreases r_nat
      {
          let bit = if r_nat % 2 == 1 { '1' } else { '0' };
          bits.push(bit);
          r_nat = r_nat / 2;
      }
  }
  let mut res = Vec::<char>::new();
  while bits.len() > 0
      invariant
          bits.len() >= 0,
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
