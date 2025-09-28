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
/* helper modified by LLM (iteration 10): Fix type casting by using usize for executable indexing */
fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures
        res@ == s,
        valid_bit_string(res@)
{
    let mut vec = Vec::new();
    let mut i = 0usize;
    while i < s.len()
        invariant
            i <= s.len(),
            vec.len() == i,
            vec@ == s.subrange(0, i as int),
            valid_bit_string(vec@)
    {
        vec.push(s[i]);
        i += 1;
    }
    vec
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
    /* code modified by LLM (iteration 10): Fix ghost variable usage for type casting */
    if sy.len() == 0 {
        return seq_to_vec(zeros(1nat));
    }
    
    if str2int(sy@) == 0nat {
        let ones = vec!['1'];
        return ones;
    }
    
    if str2int(sy@) == 1nat {
        return sx;
    }
    
    let ghost n: nat = (sy.len() - 1) as nat;
    let power_of_2 = sy@[0] == '1' && (forall|i: int| 1 <= i < sy.len() ==> sy@[i] == '0');
    
    if power_of_2 {
        return seq_to_vec(mod_exp_pow2(sx@, sy@, n, sz@));
    }
    
    let mut sy_half = Vec::new();
    let mut carry = 0;
    
    let mut i = 0usize;
    while i < sy.len()
        invariant
            i <= sy.len(),
            sy_half.len() == i,
            valid_bit_string(sy_half@)
    {
        let ghost idx: int = i as int;
        let digit = if sy@[idx] == '1' { 1 } else { 0 };
        let sum = carry * 2 + digit;
        let quotient = sum / 2;
        carry = sum % 2;
        
        sy_half.push(if quotient == 1 { '1' } else { '0' });
        i += 1;
    }
    
    let temp = mod_exp(sx.clone(), sy_half, sz.clone());
    let squared = mod_exp(temp.clone(), vec!['1', '0'], sz.clone());
    
    if carry == 1 {
        let base_mod = mod_exp(sx, vec!['1'], sz);
        return mod_exp(vec![squared, base_mod].concat(), vec!['1'], sz);
    } else {
        return squared;
    }
}
// </vc-code>


}

fn main() {}