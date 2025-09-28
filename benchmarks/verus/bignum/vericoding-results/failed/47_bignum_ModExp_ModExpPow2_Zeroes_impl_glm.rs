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
/* helper modified by LLM (iteration 5): fix is_empty issue by checking length directly */
fn is_zero(s: &Vec<char>) -> bool {
    if s.len() == 0 {
        true
    } else {
        let mut all_zero = true;
        for i in 0..s.len() {
            if s[i] != '0' {
                all_zero = false;
                break;
            }
        }
        all_zero
    }
}

fn lsb_and_shift(s: &Vec<char>) -> (bool, Vec<char>) {
    if s.len() == 0 {
        (false, s.clone())
    } else {
        let lsb = s[s.len()-1] == '1';
        let mut shifted = s.clone();
        shifted.pop(); // remove the last character
        (lsb, shifted)
    }
}

/* helper modified by LLM (iteration 10): replace for-loop with while-loop to avoid unsupported iterator */
fn vec_char_to_u64(s: &Vec<char>) -> u64 {
    let mut res: u64 = 0;
    let mut i = 0;
    while i < s.len() {
        res = res.wrapping_mul(2);
        if s[i] == '1' {
            res = res.wrapping_add(1);
        }
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 9): manual reverse to avoid complex &mut arguments */
fn u64_to_vec_char(mut n: u64) -> Vec<char> {
    if n == 0 {
        return vec!['0'];
    }
    let mut res = Vec::new();
    while n > 0 {
        if n % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        n /= 2;
    }
    // Manually reverse the vector by swapping
    let mut i = 0;
    let mut j = res.len() - 1;
    while i < j {
        let temp = res[i];
        res[i] = res[j];
        res[j] = temp;
        i += 1;
        j -= 1;
    }
    res
}

/* helper modified by LLM (iteration 7): replace from_str_radix with custom conversion */
fn mul_mod(a: &Vec<char>, b: &Vec<char>, m: &Vec<char>) -> Vec<char> {
    let a_val = vec_char_to_u64(a);
    let b_val = vec_char_to_u64(b);
    let m_val = vec_char_to_u64(m);
    if m_val == 0 {
        // Return '0' if modulus is 0 (though spec requires m>1, so this should not happen)
        vec!['0']
    } else {
        let result = a_val.wrapping_mul(b_val) % m_val;
        u64_to_vec_char(result)
    }
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
/* code modified by LLM (iteration 9): fixed helper compilation error */
{
    if is_zero(&sy) {
        vec!['1']
    } else {
        let (lsb, shifted_sy) = lsb_and_shift(&sy);
        let temp = mod_exp(sx.clone(), shifted_sy, sz.clone());
        let temp_squared = mul_mod(&temp, &temp, &sz);
        if lsb {
            mul_mod(&temp_squared, &sx, &sz)
        } else {
            temp_squared
        }
    }
}
// </vc-code>


}

fn main() {}