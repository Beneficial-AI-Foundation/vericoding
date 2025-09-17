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
/* helper modified by LLM (iteration 6): lemma that a % m < m for m > 0 */
spec fn mod_lt(a: nat, m: nat) -> bool
    requires
        m > 0,
    ensures
        (a % m) < m,
{
    a % m < m
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
  /* code modified by LLM (iteration 6): compute modular exponent using spec nats and convert result to bits */
  let modulus: nat = Str2Int(sz@);
  let mut base: nat = Str2Int(sx@) % modulus;
  let mut exp: nat = Str2Int(sy@);
  let mut res: nat = 1 % modulus;

  proof {
      // use the requirement Str2Int(sz@) > 1 from the function precondition
      assert(modulus > 1);
      // establish modulo bounds for invariants
      assert(mod_lt(Str2Int(sx@), modulus));
      assert(Str2Int(sx@) % modulus < modulus);
      assert(res < modulus);
  }

  while exp > 0
      invariant
          res < modulus,
          base < modulus,
      decreases
          exp
  {
      if exp % 2 == 1 {
          res = (res * base) % modulus;
      }
      base = (base * base) % modulus;
      exp = exp / 2;
  }

  let mut resv = Vec::<char>::new();
  if res == 0 {
      return resv;
  }

  let mut val: nat = res;
  while val > 0
      invariant
          val >= 0,
      decreases
          val
  {
      let bit = if val % 2 == 1 { '1' } else { '0' };
      resv.insert(0, bit);
      val = val / 2;
  }

  resv
}
// </vc-code>

fn main() {}
}
