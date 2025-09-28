// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
      0nat
  } else {
      2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires
      valid_bit_string(dividend) && valid_bit_string(divisor) &&
      str2int(divisor) > 0
  ensures
      valid_bit_string(result.0) && valid_bit_string(result.1) &&
      str2int(result.0) == str2int(dividend) / str2int(divisor) &&
      str2int(result.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures
      valid_bit_string(res) &&
      str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures
      s.len() == n &&
      valid_bit_string(s) &&
      str2int(s) == 0 &&
      all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn seq_to_int(s: Seq<char>) -> int
  requires
      valid_bit_string(s)
  ensures
      result as nat == str2int(s)
  decreases s.len()
{
    let mut r: int = 0;
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            r >= 0,
        decreases s.len() - i
    {
        if s[i] == '1' {
            r = r * 2 + 1;
        } else {
            r = r * 2;
        }
        i = i + 1;
    }
    r
}

fn int_to_seq(mut n: int) -> (s: Seq<char>)
  requires
      n >= 0
  ensures
      valid_bit_string(s) && str2int(s) == result as nat
{
    // handle zero specially to return at least one '0'
    if n == 0 {
        // construct a Seq with single '0'
        let v: Vec<char> = vec!['0'];
        Seq::from(v)
    } else {
        let mut bits: Vec<char> = Vec::new();
        while n > 0
            invariant
                n >= 0,
            decreases n
        {
            if n % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            n = n / 2;
        }
        // bits are LSB..MSB, reverse to MSB..LSB
        bits.reverse();
        Seq::from(bits)
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
      sy.len() > 0 && str2int(sz) > 1
  ensures
      valid_bit_string(res) &&
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  // impl-start
  let a: int = seq_to_int(sx);
  let mut base: int = a % (seq_to_int(sz));
  let mut exp: int = seq_to_int(sy);
  let m: int = seq_to_int(sz);
  // compute base^exp mod m using binary exponentiation
  let mut result: int = 1 % m;
  while exp > 0
      invariant
          result >= 0,
      decreases exp
  {
      if exp % 2 == 1 {
          result = (result * base) % m;
      }
      base = (base * base) % m;
      exp = exp / 2;
  }
  int_to_seq(result)
  // impl-end
}
// </vc-code>


}

fn main() {}