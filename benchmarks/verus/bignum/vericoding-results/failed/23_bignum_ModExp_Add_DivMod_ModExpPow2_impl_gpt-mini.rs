// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires
      valid_bit_string(s1) && valid_bit_string(s2)
  ensures
      valid_bit_string(res) &&
      str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
      (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
      sy.len() == n + 1 &&
      str2int(sz) > 1
  ensures
      valid_bit_string(res) &&
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): executable conversions and modular exponentiation */
fn seq_to_nat_exec(s: Seq<char>) -> nat
  requires
      valid_bit_string(s)
  decreases s.len()
{
    let mut i: int = 0;
    let mut acc: nat = 0;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
        decreases s.len() - i
    {
        let bit_seq = s.subrange(i, i + 1);
        let add = if bit_seq == seq!['1'] { 1 } else { 0 };
        acc = acc * 2 + add;
        i = i + 1;
    }
    acc
}

fn nat_to_seq_exec(n: nat) -> Seq<char>
  decreases n
{
    let mut v = Vec::<char>::new();
    let mut m = n;
    if m == 0 {
        v.push('0');
    } else {
        while m > 0
            invariant
                m >= 0,
            decreases m
        {
            let bit = if m % 2 == 1 { '1' } else { '0' };
            v.push(bit);
            m = m / 2;
        }
        v.reverse();
    }
    v.to_seq()
}

fn pow_mod_exec(base: nat, exp: nat, modu: nat) -> nat
  requires
      modu > 0
  decreases exp
{
    if exp == 0 { 1 % modu } else {
        let half = pow_mod_exec(base, exp / 2, modu);
        let res0 = (half * half) % modu;
        if exp % 2 == 1 { (res0 * (base % modu)) % modu } else { res0 }
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
  /* code modified by LLM (iteration 10): use executable helpers to compute modular exponentiation */
  let base = seq_to_nat_exec(sx);
  let exp = seq_to_nat_exec(sy);
  let modu = seq_to_nat_exec(sz);
  let r = pow_mod_exec(base % modu, exp, modu);
  nat_to_seq_exec(r)
}
// </vc-code>


}

fn main() {}