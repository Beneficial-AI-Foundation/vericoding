// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, (s.len() - 1) as int)) + (if s[(s.len() - 1) as int] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatches by using proper nat literals and sequence indexing */
fn int2str(n: nat) -> (result: Seq<char>)
    ensures valid_bit_string(result) && str2int(result) == n
    decreases n
{
    if n == 0nat {
        seq!['0']
    } else if n == 1nat {
        seq!['1']
    } else {
        int2str(n / 2nat).add(seq![if n % 2nat == 0nat { '0' } else { '1' }])
    }
}

fn compare_bit_strings(a: &Seq<char>, b: &Seq<char>) -> (result: bool)
    requires valid_bit_string(*a) && valid_bit_string(*b)
    ensures result == (str2int(*a) < str2int(*b))
{
    if a.len() < b.len() {
        true
    } else if a.len() > b.len() {
        false
    } else {
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == b.len(),
                forall|j: int| 0 <= j < i ==> a@[j] == b@[j]
        {
            if a@[i as int] < b@[i as int] {
                return true;
            } else if a@[i as int] > b@[i as int] {
                return false;
            }
            i += 1;
        }
        false
    }
}

fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
    ensures result@ == s
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            v@ == s.subrange(0, i)
    {
        v.push(s[i]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
      sy@.len() > 0 && str2int(sz@) > 1
  ensures 
      valid_bit_string(res@) &&
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type mismatches and sequence conversion issues */
    if str2int(sy@) == 0nat {
        return vec!['1'];
    }
    
    if str2int(sx@) == 0nat {
        return vec!['0'];
    }
    
    if str2int(sy@) == 1nat {
        let (_, remainder) = div_mod(sx@, sz@);
        return seq_to_vec(remainder);
    }
    
    let last_idx: int = (sy@.len() - 1) as int;
    let half_y = if sy@[last_idx] == '0' {
        seq_to_vec(sy@.subrange(0int, last_idx))
    } else {
        let mut temp = sy.clone();
        temp[last_idx as usize] = '0';
        let (quotient, _) = div_mod(temp@, seq!['1', '0']);
        seq_to_vec(quotient)
    };
    
    let half_result = mod_exp(sx.clone(), half_y, sz.clone());
    let squared_result = {
        let temp = int2str(str2int(half_result@) * str2int(half_result@));
        let (_, remainder) = div_mod(temp, sz@);
        seq_to_vec(remainder)
    };
    
    if sy@[last_idx] == '0' {
        squared_result
    } else {
        let temp = int2str(str2int(squared_result@) * str2int(sx@));
        let (_, remainder) = div_mod(temp, sz@);
        seq_to_vec(remainder)
    }
}
// </vc-code>


}

fn main() {}