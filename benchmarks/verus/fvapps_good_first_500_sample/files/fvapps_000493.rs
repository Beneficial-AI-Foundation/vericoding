// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_char(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] == c { 1nat } else { 0nat }) + count_char(s.skip(1), c)
    }
}

spec fn contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

fn reverse_parentheses(s: &str) -> (result: String)
    ensures 
        result@.len() + count_char(s@, '(') + count_char(s@, ')') == s@.len(),
        !contains_char(result@, '('),
        !contains_char(result@, ')'),
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
    // let test1 = reverse_parentheses("(abcd)");
    // println!("Test 1: {}", test1);
    
    // let test2 = reverse_parentheses("(u(love)i)");
    // println!("Test 2: {}", test2);
    
    // let test3 = reverse_parentheses("a(bcdefghijkl(mno)p)q");
    // println!("Test 3: {}", test3);
}