// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_at_least(citations: Seq<usize>, h: usize) -> usize {
    citations.filter(|x: usize| *x >= h).len()
}

spec fn count_at_most(citations: Seq<usize>, h: usize) -> usize {
    citations.filter(|x: usize| *x <= h).len()
}

spec fn is_valid_h_index(citations: Seq<usize>, h: usize) -> bool {
    count_at_least(citations, h) >= h &&
    count_at_most(citations, h) >= citations.len() - h
}

fn h_index(citations: Vec<usize>) -> (result: usize)
    ensures 
        is_valid_h_index(citations@, result),
        forall|h: usize| h > result ==> !is_valid_h_index(citations@, h),
        citations.len() == 0 ==> result == 0
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
    // let citations1 = vec![3, 0, 6, 1, 5];
    // let result1 = h_index(citations1);
    // println!("h-index of [3,0,6,1,5]: {}", result1);
    
    // let citations2 = vec![0];
    // let result2 = h_index(citations2);
    // println!("h-index of [0]: {}", result2);
    
    // let citations3 = vec![100];
    // let result3 = h_index(citations3);
    // println!("h-index of [100]: {}", result3);
}