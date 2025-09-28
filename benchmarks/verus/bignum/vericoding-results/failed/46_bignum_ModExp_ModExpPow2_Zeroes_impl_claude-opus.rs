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
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): Added decreases clauses to while loops */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let res = vec!['1'];
            proof {
                assert(str2int(sy@) == 0nat);
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
                assert(str2int(res@) == 1nat);
                assert(1nat % str2int(sz@) == 1nat) by {
                    assert(str2int(sz@) > 1nat);
                }
            }
            return res;
        } else {
            let res = sx.clone();
            proof {
                assert(sy[0] == '1');
                assert(str2int(sy@) == 1nat);
                assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
            }
            return res;
        }
    }
    
    let last_bit = sy[sy.len() - 1];
    let mut sy_div2_vec = Vec::new();
    let mut i: usize = 0;
    while i < sy.len() - 1
        invariant
            0 <= i <= sy.len() - 1,
            sy_div2_vec.len() == i,
            forall|j: int| 0 <= j < i ==> sy_div2_vec[j] == sy[j],
        decreases sy.len() - 1 - i
    {
        sy_div2_vec.push(sy[i]);
        i = i + 1;
    }
    
    let temp = mod_exp(sx.clone(), sy_div2_vec, sz.clone());
    
    // For squaring temp, we need to create a power-of-2 exponent
    let mut pow2_exp = Vec::new();
    pow2_exp.push('1');
    let mut j: usize = 0;
    while j < sy.len() - 1
        invariant
            0 <= j <= sy.len() - 1,
            pow2_exp.len() == j + 1,
            pow2_exp[0] == '1',
            forall|k: int| 1 <= k < pow2_exp.len() ==> pow2_exp[k] == '0',
        decreases sy.len() - 1 - j
    {
        pow2_exp.push('0');
        j = j + 1;
    }
    
    let temp_sq = mod_exp(temp.clone(), pow2_exp, sz.clone());
    
    if last_bit == '0' {
        proof {
            assert(str2int(sy@) == 2nat * str2int(sy_div2_vec@));
            assert(exp_int(str2int(sx@), str2int(sy@)) == exp_int(exp_int(str2int(sx@), str2int(sy_div2_vec@)), 2nat));
        }
        temp_sq
    } else {
        // Multiply temp_sq by sx
        let mut exp_one = Vec::new();
        exp_one.push('1');
        let result = mod_exp(sx.clone(), exp_one, sz.clone());
        
        proof {
            assert(str2int(sy@) == 2nat * str2int(sy_div2_vec@) + 1nat);
            assert(exp_int(str2int(sx@), str2int(sy@)) == str2int(sx@) * exp_int(str2int(sx@), 2nat * str2int(sy_div2_vec@)));
        }
        result
    }
}
// </vc-code>


}

fn main() {}