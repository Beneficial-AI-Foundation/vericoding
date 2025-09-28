// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): convert nat to bit sequence and correctness proof */
spec fn nat_to_bits(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        let prefix = nat_to_bits(q);
        prefix + seq![ if r == 1 { '1' } else { '0' } ]
    }
}

proof fn nat_to_bits_correct(n: nat)
  ensures
    str2int(nat_to_bits(n)) == n
  decreases n
{
    if n == 0 {
        assert(str2int(nat_to_bits(0)) == 0);
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        nat_to_bits_correct(q);
        assert(str2int(nat_to_bits(q)) == q);
        assert(str2int(nat_to_bits(q) + seq![ if r == 1 { '1' } else { '0' } ]) ==
               2nat * str2int(nat_to_bits(q)) + (if r == 1 { 1nat } else { 0nat }));
        assert(2nat * q + r == n);
        assert(str2int(nat_to_bits(q) + seq![ if r == 1 { '1' } else { '0' } ]) == n);
    }
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): corrected idx type to nat and fixed indexing for Seq<char> */
  let mut res: Seq<char> = seq!['1'];
  let (_, b0) = div_mod(sx, sz);
  let mut base: Seq<char> = b0;
  let mut idx: nat = sy.len();

  while idx > 0
      invariant
          valid_bit_string(res),
          valid_bit_string(base),
          idx <= sy.len(),
      decreases idx
  {
      idx = idx - 1;
      if sy[idx] == '1' {
          let tmp = mul(res, base);
          let (_, rtmp) = div_mod(tmp, sz);
          res = rtmp;
      }
      let sq = mul(base, base);
      let (_, rsq) = div_mod(sq, sz);
      base = rsq;
  }

  res
}

// </vc-code>


}

fn main() {}