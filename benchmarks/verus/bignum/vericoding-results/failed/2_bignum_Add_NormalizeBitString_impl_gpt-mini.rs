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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed nat literal usage in nat_to_vec */
fn vec_to_nat(v: &Vec<char>) -> (n: nat)
  requires
    valid_bit_string(v@),
  ensures
    n == str2int(v@)
{
    str2int(v@)
}

fn nat_to_vec(n: nat) -> (res: Vec<char>)
  ensures
    valid_bit_string(res@),
    str2int(res@) == n
  decreases n
{
    if n == 0nat {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else {
        let prefix = nat_to_vec(n / 2nat);
        let bit = if n % 2nat == 1nat { '1' } else { '0' };
        let mut result = prefix.clone();
        result.push(bit);
        proof {
            assert(str2int(prefix@) == n / 2nat);
            assert(str2int(result@) == 2nat * str2int(prefix@) + (if bit == '1' { 1nat } else { 0nat }));
            assert(str2int(result@) == n);
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): compute numeric sum via helpers and convert back to bit-string */
  let n1 = vec_to_nat(&s1);
  let n2 = vec_to_nat(&s2);
  let sum = n1 + n2;
  nat_to_vec(sum)
}
// </vc-code>


}

fn main() {}