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
/* helper modified by LLM (iteration 6): convert bit slice to u128 */
exec fn run_Str2Int_u128(s: &[char]) -> (res: u128)
    ensures
        (res as nat) == Str2Int(s@),
    decreases
        s.len()
{
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            (acc as nat) == Str2Int(s@.subrange(0, i as int)),
        decreases
            s.len() - i
    {
        let bit = if s[i] == '1' { 1u128 } else { 0u128 };
        acc = acc * 2 + bit;
        i += 1;
    }
    acc
}

/* helper modified by LLM (iteration 6): convert u128 to bit Vec<char> (MSB..LSB) */
exec fn u128_to_bits(mut n: u128) -> (v: Vec<char>)
    ensures
        Str2Int(v@) == (n as nat),
    decreases
        n
{
    let mut rev = Vec::<char>::new();
    if n == 0 {
        let mut z = Vec::<char>::new();
        z.push('0');
        return z;
    }
    while n != 0u128
        invariant
            (forall |i: int| 0 <= i && i < rev.len() as int ==> (rev.index(i) == '0' || rev.index(i) == '1')),
        decreases
            n
    {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        rev.push(bit);
        n /= 2;
    }
    let mut vfinal = Vec::<char>::new();
    let mut j: usize = rev.len();
    while j > 0
        invariant
            j <= rev.len(),
        decreases
            j
    {
        j -= 1;
        vfinal.push(rev[j]);
    }
    vfinal
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 6): modular exponentiation with proofs tying runtime helpers to specs */
  let x = run_Str2Int_u128(sx);
  let m = run_Str2Int_u128(sz);
  proof {
      // relate runtime m to the spec-level Str2Int(sz@) so we can use the precondition Str2Int(sz@) > 1
      assert((m as nat) == Str2Int(sz@));
      assert(Str2Int(sz@) > 1);
      assert((m as nat) > 1);
  }
  let mut base: u128 = x % m;
  let mut res_nat: u128 = 1 % m;
  let len = sy.len();
  let mut i: usize = 0;
  while i < len
      invariant
          i <= len,
      decreases
          len - i
  {
      let idx = len - 1 - i;
      // idx is in-bounds because i < len
      if sy[idx] == '1' {
          res_nat = (res_nat * base) % m;
      }
      base = (base * base) % m;
      i += 1;
  }
  let res = u128_to_bits(res_nat);
  res
}
// </vc-code>

fn main() {}
}
