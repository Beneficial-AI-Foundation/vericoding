// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn string_contains_digit(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_digit(s[i])
}

spec fn drop_leading_zeros_spec(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq!['0']
    } else if s[0] == '0' {
        drop_leading_zeros_spec(s.skip(1))
    } else {
        s
    }
}

spec fn final_result_spec(s: Seq<char>) -> Seq<char> {
    let dropped = drop_leading_zeros_spec(s);
    if dropped.len() == 0 {
        seq!['0']
    } else {
        dropped
    }
}

fn remove_k_digits(num: &str, k: usize) -> (result: String)
    requires 
        k <= num@.len(),
        string_contains_digit(num@),
    ensures 
        k == 0 ==> result@ == final_result_spec(num@),
        k == num@.len() ==> result@ == seq!['0'],
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
    // // Apps difficulty: interview
    // // Assurance level: unguarded
    // 
    // println!("{}", remove_k_digits("1432219", 3)); // Should print "1219"
    // println!("{}", remove_k_digits("10200", 1));   // Should print "200"
    // println!("{}", remove_k_digits("10", 2));      // Should print "0"
}