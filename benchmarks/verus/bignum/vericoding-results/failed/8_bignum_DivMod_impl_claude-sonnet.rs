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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed nat literal syntax by removing 'nat' suffixes */
fn int2str(n: usize) -> (result: Vec<char>)
    ensures
        valid_bit_string(result@),
        str2int(result@) == n,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant
                temp <= n,
                valid_bit_string(digits@),
            decreases temp
        {
            if temp % 2 == 0 {
                digits.push('0');
            } else {
                digits.push('1');
            }
            temp = temp / 2;
        }
        let mut result = Vec::new();
        let mut i = digits.len();
        while i > 0
            invariant
                i <= digits.len(),
                valid_bit_string(result@),
            decreases i
        {
            i = i - 1;
            result.push(digits[i]);
        }
        proof {
            assert(valid_bit_string(result@));
            assert(str2int(result@) == n);
        }
        result
    }
}

fn nat_to_usize(n: nat) -> (result: usize)
    requires n <= usize::MAX,
    ensures result == n,
{
    if n == 0 {
        0
    } else {
        let mut val = 0usize;
        let mut temp = n;
        let mut power = 1usize;
        while temp > 0
            invariant
                temp <= n,
                power > 0,
            decreases temp
        {
            if temp % 2 == 1 {
                val = val + power;
            }
            temp = temp / 2;
            if temp > 0 {
                power = power * 2;
            }
        }
        val
    }
}

fn compare_bit_strings(a: &Vec<char>, b: &Vec<char>) -> (result: bool)
    requires
        valid_bit_string(a@),
        valid_bit_string(b@),
    ensures
        result == (str2int(a@) >= str2int(b@)),
{
    if a.len() != b.len() {
        a.len() > b.len()
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] == b[j],
            decreases a.len() - i
        {
            if a[i] != b[i] {
                return a[i] == '1';
            }
            i = i + 1;
        }
        true
    }
}

fn subtract_bit_strings(a: Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
    requires
        valid_bit_string(a@),
        valid_bit_string(b@),
        str2int(a@) >= str2int(b@),
        str2int(a@) - str2int(b@) <= usize::MAX,
    ensures
        valid_bit_string(result@),
        str2int(result@) == str2int(a@) - str2int(b@),
{
    let diff_nat = str2int(a@) - str2int(b@);
    let diff_usize = nat_to_usize(diff_nat);
    int2str(diff_usize)
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0,
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed nat literal syntax by removing 'nat' suffixes */
    let dividend_nat = str2int(dividend@);
    let divisor_nat = str2int(divisor@);
    
    let dividend_val = nat_to_usize(dividend_nat);
    let divisor_val = nat_to_usize(divisor_nat);
    
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let quotient = int2str(quotient_val);
    let remainder = int2str(remainder_val);
    
    proof {
        assert(valid_bit_string(quotient@));
        assert(valid_bit_string(remainder@));
        assert(str2int(quotient@) == quotient_val);
        assert(str2int(remainder@) == remainder_val);
        assert(quotient_val == dividend_val / divisor_val);
        assert(remainder_val == dividend_val % divisor_val);
    }
    
    (quotient, remainder)
}
// </vc-code>


}

fn main() {}