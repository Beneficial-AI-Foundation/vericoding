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
/* helper modified by LLM (iteration 5): Implemented helper functions reverse_seq, to_bit_string, and to_vec, and properly implemented div_mod and mod_exp_pow2 using nat operations to avoid bit-level complexities */
fn reverse_seq(s: Seq<char>) -> Seq<char>
{
    let mut reversed = Seq::new();
    let mut i = s.len() as int;
    while i > 0
        decreases i
    {
        i -= 1;
        reversed = reversed.push(s[i as nat]);
    }
    reversed
}

fn to_bit_string(n: nat) -> Seq<char>
{
    if n == 0 {
        Seq::empty()
    } else {
        let mut bits: Vec<char> = Vec::new();
        let mut current = n;
        while current > 0
            invariant current >= 0
            decreases current
        {
            bits.push(if current % 2nat == 1nat { '1' } else { '0' });
            current = current / 2nat;
        }
        reverse_seq(bits@)
    }
}

fn to_vec(s: Seq<char>) -> Vec<char>
{
    s.iter().cloned().collect()
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
    let dividend_int = str2int(dividend);
    let divisor_int = str2int(divisor);
    let quotient_int = dividend_int / divisor_int;
    let remainder_int = dividend_int % divisor_int;
    let quotient = to_bit_string(quotient_int);
    let remainder = to_bit_string(remainder_int);
    (quotient, remainder)
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
    let mut result = sx;
    let mut i = 0nat;
    while i < n
        invariant
            valid_bit_string(result) &&
            i <= n,
            str2int(result) == exp_int(str2int(sx), exp_int(2nat, i)) % str2int(sz)
        decreases n - i
    {
        let current_int = str2int(result);
        let sz_int = str2int(sz);
        let new_result_int = (current_int * current_int) % sz_int;
        result = to_bit_string(new_result_int);
        i += 1;
    }
    result
}
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
    let mut result = Vec::with_capacity(1);
    result.push('1');
    let mut base = sx.clone();
    let mut exp_vec = sy.clone();
    while exp_vec.len() > 0
        invariant
            valid_bit_string(result@) && valid_bit_string(base@) &&
            exp_vec.len() >= 0 && exp_vec@.len() <= sy@.len(),
            str2int(result@) == exp_int(str2int(sx@), str2int(sy@.subrange(sy@.len() - exp_vec.len(), sy@.len()))) % str2int(sz@)
        decreases exp_vec.len()
    {
        if exp_vec.last().unwrap() == '1' {
            let result_int = str2int(result@);
            let base_int = str2int(base@);
            let sz_int = str2int(sz@);
            let new_result_int = (result_int * base_int) % sz_int;
            let result_seq = to_bit_string(new_result_int);
            result = to_vec(result_seq);
        }
        let base_int = str2int(base@);
        let sz_int = str2int(sz@);
        let new_base_int = (base_int * base_int) % sz_int;
        let base_seq = to_bit_string(new_base_int);
        base = to_vec(base_seq);
        exp_vec.truncate(exp_vec.len() - 1);
    }
    result
}
// </vc-code>


}

fn main() {}