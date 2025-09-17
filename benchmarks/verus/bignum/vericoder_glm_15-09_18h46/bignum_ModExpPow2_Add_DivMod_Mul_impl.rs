
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn Str2Int_exec(s: &Vec<char>) -> (n: nat)
  requires ValidBitString(s@)
  ensures n == Str2Int(s@)
{
  let mut n = 0;
  for i in 0..s.len()
      invariant n == Str2Int(s@.subrange(0, i as int))
  {
      let c = s[i];
      if c == '1' {
          n = n * 2 + 1;
      } else {
          n = n * 2;
      }
  }
  n
}

exec fn Int2BitString(n: nat, L: nat) -> (s: Vec<char>)
  ensures s@.len() == L,
  ensures ValidBitString(s@),
  ensures Str2Int(s@) == n % (2 as nat ^ L)
{
  let m = n % (2 as nat ^ L);
  let mut n_remaining = m;
  let mut bits_value = 0;
  let mut bits = Vec::new();
  for i in 0..L
      invariant 0 <= i <= L,
      invariant bits.len() == i,
      invariant n_remaining * (2 as nat ^ i) + bits_value == m,
      invariant forall |j: int| 0 <= j < i ==> (bits[j] == '0' || bits[j] == '1')
  {
      let bit = n_remaining % 2;
      n_remaining = n_remaining / 2;
      let power = 2 as nat ^ i;
      if bit == 1 {
          bits.push('1');
          bits_value = bits_value + power;
      } else {
          bits.push('0');
      }
  }
  bits.reverse();
  bits
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let n_a = Str2Int_exec(a);
  let n_b = Str2Int_exec(b);
  let sum = n_a + n_b;
  let L = a.len().max(b.len()) + 1;
  let res = Int2BitString(sum, L);
  res
}
// </vc-code>

fn main() {}
}

