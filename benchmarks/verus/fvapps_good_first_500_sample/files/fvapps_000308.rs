// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_prefix_of(prefix: Seq<char>, s: Seq<char>) -> bool {
    prefix.len() <= s.len() && 
    forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == s[i]
}

spec fn is_suffix_of(suffix: Seq<char>, s: Seq<char>) -> bool {
    suffix.len() <= s.len() && 
    forall|i: int| 0 <= i < suffix.len() ==> suffix[i] == s[s.len() - suffix.len() + i]
}

fn longest_prefix(s: Vec<char>) -> (result: Vec<char>)
    requires s.len() > 0,
    ensures
        result.len() < s.len(),
        is_prefix_of(result@, s@),
        result.len() == 0 || is_suffix_of(result@, s@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let s1: Vec<char> = "level".chars().collect();
    // let result1 = longest_prefix(s1);
    // println!("{:?}", result1);
    
    // let s2: Vec<char> = "ababab".chars().collect();
    // let result2 = longest_prefix(s2);
    // println!("{:?}", result2);
    
    // let s3: Vec<char> = "leetcodeleet".chars().collect();
    // let result3 = longest_prefix(s3);
    // println!("{:?}", result3);
}