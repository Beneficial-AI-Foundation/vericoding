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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
      valid_bit_string(dividend) && valid_bit_string(divisor),
      str2int(divisor) > 0,
  ensures 
      valid_bit_string(res.0) && valid_bit_string(res.1),
      str2int(res.0) == str2int(dividend) / str2int(divisor),
      str2int(res.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
      s.len() == n,
      valid_bit_string(s),
      str2int(s) == 0,
      all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): convert between Vec<char> and nat, without nat suffixes */

fn vec2nat(v: &Vec<char>) -> nat {
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < v.len() {
        let b: nat = if v[i] == '1' { 1 } else { 0 };
        acc = acc * 2 + b;
        i = i + 1;
    }
    acc
}

fn nat2vec(n: nat) -> Vec<char>
  decreases n
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else {
        let q: nat = n / 2;
        let r_is_one = (n % 2 == 1);
        let mut prefix = nat2vec(q);
        prefix.push(if r_is_one { '1' } else { '0' });
        prefix
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
      sy.len() > 0 && str2int(sz@) > 1,
  ensures 
      valid_bit_string(res@),
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): implement modular exponentiation using helpers and remove nat suffixes */

    let mut base: nat = vec2nat(&sx);
    let mut exp: nat = vec2nat(&sy);
    let m: nat = vec2nat(&sz);

    let mut res_nat: nat = 1;

    while exp > 0
        invariant
            res_nat >= 0,
            exp >= 0,
        decreases exp
    {
        if exp % 2 == 1 {
            res_nat = (res_nat * base) % m;
        }
        base = (base * base) % m;
        exp = exp / 2;
    }

    nat2vec(res_nat)
}
// </vc-code>


}

fn main() {}