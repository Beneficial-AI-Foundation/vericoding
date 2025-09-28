// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed nat literal syntax and vector access errors */
proof fn lemma_exp_int_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn lemma_str2int_empty()
    ensures str2int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_mod_exp_base_case(sx: Seq<char>, sz: Seq<char>)
    requires valid_bit_string(sx), valid_bit_string(sz), str2int(sz) > 1
    ensures exp_int(str2int(sx), 0) % str2int(sz) == 1
{
    lemma_exp_int_zero(str2int(sx));
}

fn int_to_binary_string(n: nat) -> (res: Vec<char>)
    ensures valid_bit_string(res@), str2int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant valid_bit_string(result@)
        {
            if temp % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ == s
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
                  result@ == s.subrange(0, i as int)
    {
        result.push(s[i as int]);
        i = i + 1;
    }
    result
}
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
    /* code modified by LLM (iteration 10): fixed nat literal syntax and sequence access errors */
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if str2int(sy@) == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let result_mod = str2int(sx@) % str2int(sz@);
        return int_to_binary_string(result_mod);
    }
    
    let ghost start_idx = 1int;
    let ghost end_idx = sy@.len() as int;
    let sy_tail = sy@.subrange(start_idx, end_idx);
    let sy_tail_vec = seq_to_vec(sy_tail);
    let recursive_result = mod_exp(sx.clone(), sy_tail_vec, sz.clone());
    
    if sy[0] == '0' {
        return recursive_result;
    } else {
        let base_mod = str2int(sx@) % str2int(sz@);
        let combined = (base_mod * str2int(recursive_result@)) % str2int(sz@);
        return int_to_binary_string(combined);
    }
}
// </vc-code>


}

fn main() {}