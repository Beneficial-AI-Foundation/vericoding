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
/* helper modified by LLM (iteration 9): predicate for bit characters */
spec fn IsBitChar(c: char) -> bool
{
    c == '0' || c == '1'
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): modular exponentiation using nat literals and bit conversion */
  let m: nat = Str2Int(sz@);
  let mut acc: nat = 1nat % m;
  let mut b: nat = Str2Int(sx@) % m;
  let mut e: nat = Str2Int(sy@);

  while e > 0nat
      invariant
          m > 1nat,
          acc < m,
          b < m,
      decreases e
  {
      if e % 2nat == 1nat {
          acc = (acc * b) % m;
      }
      b = (b * b) % m;
      e = e / 2nat;
  }

  let mut tmp = Vec::<char>::new();
  if acc == 0nat {
      // represent zero as empty sequence per Str2Int
  } else {
      let mut x: nat = acc;
      while x > 0nat
          invariant
              0nat <= x,
          decreases x
      {
          if x % 2nat == 1nat {
              tmp.push('1');
          } else {
              tmp.push('0');
          }
          x = x / 2nat;
      }
  }

  let mut res = Vec::<char>::new();
  let len_tmp: usize = tmp.len();
  let mut j: usize = 0usize;
  while j < len_tmp
      invariant
          j <= len_tmp,
      decreases len_tmp - j
  {
      let idx: usize = len_tmp - 1usize - j;
      res.push(tmp[idx]);
      j += 1usize;
  }

  res
}

// </vc-code>

fn main() {}
}
