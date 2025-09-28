// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
proof fn sub_digit_and_borrow(digit1: nat, digit2: nat, borrow_in: nat) -> (result_digit: nat, borrow_out: nat)
    requires
        digit1 == 0 || digit1 == 1,
        digit2 == 0 || digit2 == 1,
        borrow_in == 0 || borrow_in == 1,
    ensures
        (result_digit == 0 || result_digit == 1) &&
        (borrow_out == 0 || borrow_out == 1) &&
        (digit1 + borrow_in) == (digit2 + result_digit + (borrow_out) * 2)
{
    let sum = digit1 + borrow_in;
    if sum >= digit2 {
        (sum - digit2, 0)
    } else {
        (sum + 2 - digit2, 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    str2int(s1@) >= str2int(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) - str2int(s2@),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    let mut borrow: nat = 0nat;

    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };

    while i < max_len
        invariant
            0 <= i <= max_len,
            borrow == 0 || borrow == 1,
            (result@).len() == i,
            valid_bit_string(result@)
            
        decreases max_len - i
    {
        let d1 = if i < len1 { if s1[len1 - 1 - i as int] == '1' { 1nat } else { 0nat } } else { 0nat };
        let d2 = if i < len2 { if s2[len2 - 1 - i as int] == '1' { 1nat } else { 0nat } } else { 0nat };
        
        proof {
            assert(d1 == 0 || d1 == 1);
            assert(d2 == 0 || d2 == 1);
        }

        let (res_digit, next_borrow): (nat, nat) = sub_digit_and_borrow(d1, d2, borrow);
        borrow = next_borrow;
        result.insert(0, if res_digit == 1 { '1' } else { '0' });
        i = i + 1;
    }

    let mut leading_zeros = 0;
    while leading_zeros < result.len() - 1 && result[leading_zeros as int] == '0' {
        leading_zeros = leading_zeros + 1;
    }
    result.split_off(leading_zeros as int);

    result
}
// </vc-code>


}

fn main() {}