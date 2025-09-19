// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_to_nat(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let digit = (s[0] as u8 - '0' as u8) as nat;
        digit * pow(10, (s.len() - 1) as nat) + string_to_nat(s.skip(1))
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

spec fn count_digit_in_string(s: Seq<char>, d: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let count_rest = count_digit_in_string(s.skip(1), d);
        if s[0] == d {
            1 + count_rest
        } else {
            count_rest
        }
    }
}

spec fn count_digit_in_list(digits: Seq<u8>, d: u8) -> nat
    decreases digits.len()
{
    if digits.len() == 0 {
        0
    } else {
        let count_rest = count_digit_in_list(digits.skip(1), d);
        if digits[0] == d {
            1 + count_rest
        } else {
            count_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn largest_multiple_of_three(digits: Vec<u8>) -> (result: Option<String>)
    requires
        digits.len() >= 1,
        digits.len() <= 10000,
        forall|i: int| 0 <= i < digits.len() ==> digits[i] <= 9,
    ensures
        match result {
            Some(s) => {
                /* Result is multiple of three */
                string_to_nat(s@) % 3 == 0 &&
                /* Result uses valid digits */
                forall|d: u8| d <= 9 ==> count_digit_in_string(s@, (d + '0' as u8) as char) <= count_digit_in_list(digits@, d) &&
                /* Handles leading zeros properly */
                (s@ == seq!['0'] || s@.len() == 0 || s@[0] != '0')
            },
            None => true
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = largest_multiple_of_three(vec![9, 8, 1]);
    // println!("Result 1: {:?}", result1);
    
    // let result2 = largest_multiple_of_three(vec![8, 6, 7, 1, 0]);
    // println!("Result 2: {:?}", result2);
    
    // let result3 = largest_multiple_of_three(vec![1]);
    // println!("Result 3: {:?}", result3);
}