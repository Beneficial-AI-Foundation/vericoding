// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_unique_chars(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let rest_count = count_unique_chars(s.skip(1));
        if s.skip(1).contains(first) {
            rest_count
        } else {
            rest_count + 1
        }
    }
}

fn max_repeated_chars_with_swap(s: Vec<char>) -> (result: usize)
    requires s.len() > 0,
    ensures 
        1 <= result && result <= s.len(),
        (count_unique_chars(s@) == 1 ==> result == s.len()),
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
    // let result1 = max_repeated_chars_with_swap(vec!['a', 'b', 'a', 'b', 'a']);
    // println!("{}", result1); // Should print 3
    
    // let result2 = max_repeated_chars_with_swap(vec!['a', 'a', 'a', 'b', 'a', 'a', 'a']);
    // println!("{}", result2); // Should print 6
    
    // let result3 = max_repeated_chars_with_swap(vec!['a', 'a', 'a', 'b', 'b', 'a', 'a', 'a']);
    // println!("{}", result3); // Should print 4
}