// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_lowercase_letter(c: char) -> bool {
    let n = c as u32;
    97 <= n && n <= 122
}

spec fn count_descending_pairs(s: Seq<char>) -> nat 
    decreases s.len()
{
    if s.len() <= 1 {
        0
    } else {
        let first_pair: nat = if s[0] > s[1] { 1 } else { 0 };
        first_pair + count_descending_pairs(s.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn find_k_descending_pairs(k: u32) -> (result: Vec<char>)
    requires k > 0,
    ensures 
        count_descending_pairs(result@) == k,
        forall|c: char| result@.contains(c) ==> is_lowercase_letter(c),
        result.len() == k + 1 + (if k > 25 { (k - 26) / 25 + 1 } else { 0 }),
        forall|c: char| result@.contains(c) ==> (97 <= c as u32 && c as u32 <= 122)
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
    // let result1 = find_k_descending_pairs(1);
    // println!("{:?}", result1.iter().collect::<String>());
    
    // let result2 = find_k_descending_pairs(2); 
    // println!("{:?}", result2.iter().collect::<String>());
    
    // let result3 = find_k_descending_pairs(3);
    // println!("{:?}", result3.iter().collect::<String>());
}