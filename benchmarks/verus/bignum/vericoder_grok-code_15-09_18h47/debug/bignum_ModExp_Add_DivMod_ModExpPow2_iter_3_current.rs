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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
exec fn shift_left(s: &[char], n: usize) -> (result: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s@) * Exp_int(2, n as nat)
    /* helper modified by LLM (iteration 3): fixed named return and corrected ensures clauses */
{
  let mut res = s.to_vec();
  for _ in 0..n {
    res.push('0');
  }
  res
}

exec fn mul_mod(a: &[char], b: &[char], z: &[char]) -> (result: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@), ValidBitString(z@), Str2Int(z@) > 1
  ensures ValidBitString(result@), Str2Int(result@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(z@)
    /* helper modified by LLM (iteration 3): changed to exec fn, named return, fixed ensures */
{
  let mut res = Vec::new();
  let mut i = 0;
  while i < b.len()
    invariant
      ValidBitString(a@), ValidBitString(b@), ValidBitString(z@),
      Str2Int(z@) > 1,
      i <= b.len(),
      ValidBitString(res@)
    decreases b.len() - i
  {
    if b[i] == '1' {
      let shifted_a = shift_left(a, i);
      res = Add(&res, &shifted_a);
    }
    i += 1;
  }
  let divmod = DivMod(&res, z);
  divmod.1
}
// </vc-helpers>

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
    /* code modified by LLM (iteration 3): kept implementation as is, compilation errors were in helpers */
    let mut result = Vec::from(['1']);
    let mut base = sx.to_vec();
    let len = sy.len();
    let mut i = 0;
    while i < len
      invariant
        ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
        sy@.len() > 0, Str2Int(sz@) > 1,
        i <= sy@.len(),
        ValidBitString(result@), ValidBitString(base@)
      decreases len - i
    {
      if sy[i] == '1' {
        result = mul_mod(&result, &base, sz);
      }
      base = mul_mod(&base, &base, sz);
      i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}
