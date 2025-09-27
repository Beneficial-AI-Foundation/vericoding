// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_papers_with_at_least_citations(citations: Seq<u32>, h: u32) -> nat {
    citations.filter(|x: u32| x >= h).len()
}

spec fn is_valid_h_index(citations: Seq<u32>, h: u32) -> bool {
    let papers_with_at_least_h = count_papers_with_at_least_citations(citations, h);
    papers_with_at_least_h >= h && (citations.len() - papers_with_at_least_h) <= h
}

fn h_index(citations: Vec<u32>) -> (result: u32)
    ensures 
        result <= citations.len(),
        is_valid_h_index(citations@, result),
        forall|h: u32| h > result ==> !is_valid_h_index(citations@, h),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {
    // #eval h_index [0, 1, 3, 5, 6]  // Expected: 3
    // #eval h_index [0]              // Expected: 0  
    // #eval h_index [5, 5, 5]        // Expected: 3
}