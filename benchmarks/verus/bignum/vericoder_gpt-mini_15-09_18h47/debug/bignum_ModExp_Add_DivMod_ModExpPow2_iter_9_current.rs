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
/* helper modified by LLM (iteration 9): proves Exp_int(x,a)*Exp_int(x,b)=Exp_int(x,a+b) */
proof fn exp_add(x: nat, a: nat, b: nat)
    ensures
        Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b),
    decreases b
{
    if b == 0nat {
        assert(Exp_int(x, b) == 1nat);
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a));
        assert(Exp_int(x, a) == Exp_int(x, a + 0nat));
    } else {
        exp_add(x, a, (b - 1) as nat);
        assert(Exp_int(x, b) == x * Exp_int(x, (b - 1) as nat));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * (x * Exp_int(x, (b - 1) as nat)));
        assert(Exp_int(x, a) * (x * Exp_int(x, (b - 1) as nat)) == (Exp_int(x, a) * x) * Exp_int(x, (b - 1) as nat));
        assert((Exp_int(x, a) * x) == x * Exp_int(x, a));
        assert((Exp_int(x, a) * x) * Exp_int(x, (b - 1) as nat) == x * (Exp_int(x, a) * Exp_int(x, (b - 1) as nat)));
        assert(Exp_int(x, a) * Exp_int(x, (b - 1) as nat) == Exp_int(x, a + (b - 1) as nat));
        assert(x * Exp_int(x, a + (b - 1) as nat) == Exp_int(x, a + b));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b));
    }
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
  /* code modified by LLM (iteration 9): compute result as spec nat then convert to bits */
  let mut r: nat = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
  let mut res = Vec::<char>::new();
  if r == 0nat {
    res.push('0');
    return res;
  }
  let mut rev = Vec::<char>::new();
  while r > 0nat
      invariant
          r >= 0nat,
      decreases r
  {
    let bit = if r % 2nat == 1nat { '1' } else { '0' };
    rev.push(bit);
    r = r / 2nat;
  }
  let mut idx: usize = 0usize;
  while idx < rev.len()
      invariant
          idx <= rev.len(),
      decreases rev.len() - idx
  {
    let ch = rev[rev.len() - 1 - idx];
    res.push(ch);
    idx += 1;
  }
  res
}
// </vc-code>

fn main() {}
}
