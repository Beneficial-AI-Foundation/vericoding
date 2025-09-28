// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed sequence indexing by using ghost variable in loop */
spec fn mod_exp_helper(x: nat, y: nat, z: nat) -> nat {
    if z <= 1 { 0nat } else if y == 0 { 1nat % z } else { (x * mod_exp_helper(x, (y - 1) as nat, z)) % z }
}

proof fn lemma_exp_pow2(n: u8)
    ensures exp_int(2nat, n as nat) == if n == 0 { 1nat } else { 2nat * exp_int(2nat, (n - 1) as nat) }
{
}

proof fn lemma_mod_exp_zero(x: nat, z: nat)
    requires z > 1
    ensures exp_int(x, 0nat) % z == 1nat % z
{
}

proof fn lemma_str2int_properties(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s) >= 0
{}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures res@ == s && valid_bit_string(res@)
{
    let mut result = Vec::new();
    let len = s.len() as usize;
    for i in 0..len
        invariant
            0 <= i <= len,
            result.len() == i,
            result@ == s.subrange(0, i as int),
            valid_bit_string(result@)
    {
        let ghost idx = i as int;
        result.push(s[idx]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed sequence indexing by using ghost variable */
    if n == 0 {
        if str2int(sy@) == 0nat {
            let result = vec!['1'];
            proof {
                lemma_mod_exp_zero(str2int(sx@), str2int(sz@));
            }
            result
        } else {
            let x_mod_z = div_mod(sx@, sz@).1;
            seq_to_vec(x_mod_z)
        }
    } else {
        if str2int(sy@) == 0nat {
            let result = vec!['1'];
            proof {
                lemma_mod_exp_zero(str2int(sx@), str2int(sz@));
            }
            result
        } else {
            let mut new_sy = Vec::new();
            for i in 0..(sy.len() - 1)
                invariant
                    0 <= i <= sy.len() - 1,
                    new_sy.len() == i,
                    new_sy@ == sy@.subrange(0, i as int)
            {
                let ghost idx = i as int;
                new_sy.push(sy@[idx]);
            }
            let sub_result = mod_exp_pow2(sx, new_sy, n - 1, sz);
            let x_times_sub = vec!['0'];
            let result = div_mod(x_times_sub@, sz@).1;
            seq_to_vec(result)
        }
    }
}
// </vc-code>


}

fn main() {}