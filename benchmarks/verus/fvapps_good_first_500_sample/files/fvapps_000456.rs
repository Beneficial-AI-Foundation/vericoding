// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_digit_char(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn count_digits(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if is_digit_char(s[0]) { 1nat } else { 0nat }) + count_digits(s.skip(1))
    }
}

spec fn last_n_chars(s: Seq<char>, n: nat) -> Seq<char> {
    if n >= s.len() {
        s
    } else {
        s.skip((s.len() - n) as int)
    }
}

fn mask_pii(s: String) -> (result: String)
    requires 
        s@.len() <= 40,
        s@.len() >= 8,
    ensures
        /* For 10-digit phone numbers (all digits) */
        (s@.len() == 10 && forall|i: int| 0 <= i < s@.len() ==> is_digit_char(s@[i])) ==>
            result@ == seq!['*', '*', '*', '-', '*', '*', '*', '-'] + last_n_chars(s@, 4),
        /* For phone numbers with more than 10 digits */
        (count_digits(s@) > 10) ==>
            result@.len() > 0 &&
            result@[0] == '+' &&
            exists|i: int| 0 <= i < result@.len() && result@[i] == '-' &&
            exists|j: int| 0 <= j < result@.len() && result@[j] == '*',
        /* For specific email example */
        s@ == "LeetCode@LeetCode.com"@ ==> result@ == "l*****e@leetcode.com"@
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = mask_pii("LeetCode@LeetCode.com".to_string());
    // println!("{}", result1); // Should print: l*****e@leetcode.com
    
    // let result2 = mask_pii("1(234)567-890".to_string()); 
    // println!("{}", result2); // Should print: ***-***-7890
    
    // let result3 = mask_pii("86-(10)12345678".to_string());
    // println!("{}", result3); // Should print: +**-***-***-5678
}