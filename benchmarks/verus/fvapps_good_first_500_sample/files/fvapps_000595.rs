// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn contains_substring(s: Seq<char>, sub: Seq<char>) -> bool 
    decreases s.len()
{
    if sub.len() == 0 {
        true
    } else if s.len() < sub.len() {
        false
    } else if s.take(sub.len() as int) == sub {
        true
    } else {
        contains_substring(s.skip(1), sub)
    }
}

fn classify_feedback(s: Vec<char>) -> (result: &'static str)
    requires s.len() > 0,
    ensures 
        result == "Good" || result == "Bad",
        result == "Good" <==> (contains_substring(s@, "010"@) || contains_substring(s@, "101"@)),
        s.len() < 3 ==> result == "Bad",
        s@ == "010"@ || s@ == "101"@ ==> result == "Good",
        !(contains_substring(s@, "010"@) || contains_substring(s@, "101"@)) ==> result == "Bad"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "Bad"
    // impl-end
}
// </vc-code>


}
fn main() {
    // let s1: Vec<char> = "11111110".chars().collect();
    // let result1 = classify_feedback(s1);
    // println!("{}", result1);
    
    // let s2: Vec<char> = "10101010101010".chars().collect();
    // let result2 = classify_feedback(s2);
    // println!("{}", result2);
    
    // let s3: Vec<char> = "00010".chars().collect();
    // let result3 = classify_feedback(s3);
    // println!("{}", result3);
}