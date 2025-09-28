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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0
  ensures 
    ({
       let (quotient, remainder) = result; 
       valid_bit_string(quotient) && valid_bit_string(remainder) &&
       str2int(quotient) == str2int(dividend) / str2int(divisor) &&
       str2int(remainder) == str2int(dividend) % str2int(divisor)
    })
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

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed indexing - use usize directly without as int conversion */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut res = Vec::new();
            res.push('1');
            proof {
                assert(sy@.len() == 1);
                assert(sy@[0] == '0');
                assert(str2int(sy@) == 0nat);
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
                assert(1nat % str2int(sz@) < str2int(sz@));
                assert(res@.len() == 1);
                assert(res@[0] == '1');
                assert(str2int(res@) == 1nat);
            }
            return res;
        } else {
            let (_, res) = div_mod(sx@, sz@);
            let mut res_vec = Vec::new();
            let res_len = res.len() as usize;
            let mut i: usize = 0;
            while i < res_len
                invariant
                    0 <= i <= res_len,
                    res_len == res.len() as usize,
                    res_vec.len() == i,
                    forall|j: int| 0 <= j < i ==> res_vec@[j] == res[j]
            {
                let ghost idx = i as int;
                res_vec.push(res[idx]);
                i = i + 1;
            }
            proof {
                assert(sy@.len() == 1);
                assert(sy@[0] == '1');
                assert(str2int(sy@) == 1nat);
                assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
                assert(str2int(res) == str2int(sx@) % str2int(sz@));
                assert(res_vec@.len() == res.len());
                assert(forall|i: int| 0 <= i < res_vec@.len() ==> res_vec@[i] == res[i]);
                assert(res_vec@ =~= res);
            }
            return res_vec;
        }
    } else {
        let mut sy_vec = Vec::new();
        let mut i: usize = 0;
        while i < sy.len()
            invariant
                0 <= i <= sy.len(),
                sy_vec.len() == i,
                forall|j: int| 0 <= j < i ==> sy_vec[j] == sy[j]
        {
            sy_vec.push(sy[i]);
            i = i + 1;
        }
        
        let ghost n = (sy.len() - 1) as nat;
        let exp2_res = mod_exp_pow2(sx@, sy_vec@, n, sz@);
        
        let mut exp2_res_vec = Vec::new();
        let exp2_res_len = exp2_res.len() as usize;
        let mut i: usize = 0;
        while i < exp2_res_len
            invariant
                0 <= i <= exp2_res_len,
                exp2_res_len == exp2_res.len() as usize,
                exp2_res_vec.len() == i,
                forall|j: int| 0 <= j < i ==> exp2_res_vec@[j] == exp2_res[j]
        {
            let ghost idx = i as int;
            exp2_res_vec.push(exp2_res[idx]);
            i = i + 1;
        }
        
        let mut sy_minus_exp2 = Vec::new();
        let ghost diff = str2int(sy@) - exp_int(2nat, n);
        
        proof {
            if diff == 0 {
                assert(str2int(sy@) == exp_int(2nat, n));
            }
        }
        
        if sy.len() == 2 && sy[0] == '1' && sy[1] == '0' {
            sy_minus_exp2.push('0');
        } else {
            let mut temp_vec = Vec::new();
            let mut borrow: bool = false;
            let mut i: usize = sy.len() - 1;
            
            loop
                invariant
                    i < sy.len(),
                    temp_vec.len() == sy.len() - 1 - i
            {
                if i == 0 {
                    break;
                }
                
                let mut digit_val: u8 = if sy[i] == '1' { 1 } else { 0 };
                
                if i == sy.len() - 1 {
                    if digit_val >= 1 {
                        digit_val = digit_val - 1;
                    } else {
                        digit_val = 1;
                        borrow = true;
                    }
                } else {
                    if borrow {
                        if digit_val >= 1 {
                            digit_val = digit_val - 1;
                            borrow = false;
                        } else {
                            digit_val = 1;
                        }
                    }
                }
                
                if digit_val == 0 {
                    temp_vec.push('0');
                } else {
                    temp_vec.push('1');
                }
                
                i = i - 1;
            }
            
            let mut j: usize = 0;
            while j < temp_vec.len() / 2
                invariant
                    0 <= j <= temp_vec.len() / 2,
                    temp_vec.len() == temp_vec.len(),
                    forall|k: int| 0 <= k < temp_vec.len() ==> (temp_vec[k] == '0' || temp_vec[k] == '1')
            {
                let temp = temp_vec[j];
                let k = temp_vec.len() - 1 - j;
                temp_vec.set(j, temp_vec[k]);
                temp_vec.set(k, temp);
                j = j + 1;
            }
            sy_minus_exp2 = temp_vec;
        }
        
        let rec_res = mod_exp(sx.clone(), sy_minus_exp2, sz.clone());
        
        let mut prod = Vec::new();
        let mut carry: u64 = 0;
        let mut i: usize = 0;
        
        while i < exp2_res_vec.len() || i < rec_res.len() || carry > 0
            invariant
                0 <= i,
                carry <= 1,
                forall|j: int| 0 <= j < prod.len() ==> (prod[j] == '0' || prod[j] == '1')
        {
            let mut digit_sum = carry;
            
            if i < exp2_res_vec.len() {
                if exp2_res_vec[i] == '1' {
                    digit_sum = digit_sum + 1;
                }
            }
            
            if i < rec_res.len() {
                if rec_res[i] == '1' {
                    digit_sum = digit_sum + 1;
                }
            }
            
            if digit_sum % 2 == 0 {
                prod.push('0');
            } else {
                prod.push('1');
            }
            
            carry = digit_sum / 2;
            i = i + 1;
        }
        
        let (_, final_res) = div_mod(prod@, sz@);
        let mut final_res_vec = Vec::new();
        let final_res_len = final_res.len() as usize;
        let mut i: usize = 0;
        while i < final_res_len
            invariant
                0 <= i <= final_res_len,
                final_res_len == final_res.len() as usize,
                final_res_vec.len() == i,
                forall|j: int| 0 <= j < i ==> final_res_vec@[j] == final_res[j]
        {
            let ghost idx = i as int;
            final_res_vec.push(final_res[idx]);
            i = i + 1;
        }
        
        proof {
            assert(str2int(sy@) == exp_int(2nat, n) + str2int(sy_minus_exp2@));
            assert(exp_int(str2int(sx@), str2int(sy@)) == exp_int(str2int(sx@), exp_int(2nat, n)) * exp_int(str2int(sx@), str2int(sy_minus_exp2@)));
            assert(str2int(exp2_res) == exp_int(str2int(sx@), exp_int(2nat, n)) % str2int(sz@));
            assert(str2int(rec_res@) == exp_int(str2int(sx@), str2int(sy_minus_exp2@)) % str2int(sz@));
            assert(final_res_vec@ =~= final_res);
        }
        
        return final_res_vec;
    }
}
// </vc-code>


}

fn main() {}