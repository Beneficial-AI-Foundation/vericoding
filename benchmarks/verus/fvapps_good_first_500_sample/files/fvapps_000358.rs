// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_duplicate(nums: Seq<u32>) -> (result: Option<u32>)
    ensures
        nums.len() == 0 ==> result == Option::<u32>::None,
        nums =~= seq![1u32, 3u32, 4u32, 2u32, 2u32] ==> result == Some(2u32),
        nums =~= seq![3u32, 1u32, 3u32, 4u32, 2u32] ==> result == Some(3u32),
        nums =~= seq![2u32, 2u32, 2u32, 2u32, 2u32] ==> result == Some(2u32),
        nums =~= seq![1u32, 1u32] ==> result == Some(1u32),
        nums =~= seq![1u32, 2u32, 3u32, 4u32, 5u32, 6u32, 7u32, 8u32, 9u32, 5u32] ==> result == Some(5u32)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


proof fn test_empty_list_return_none() {
    assert(find_duplicate(seq![]) == None::<u32>);
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_finds_duplicate_in_list1() {
    assert(find_duplicate(seq![1u32, 3u32, 4u32, 2u32, 2u32]) == Some(2u32));
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_finds_duplicate_in_list2() {
    assert(find_duplicate(seq![3u32, 1u32, 3u32, 4u32, 2u32]) == Some(3u32));
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_finds_duplicate_in_list3() {
    assert(find_duplicate(seq![2u32, 2u32, 2u32, 2u32, 2u32]) == Some(2u32));
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_finds_duplicate_in_list4() {
    assert(find_duplicate(seq![1u32, 1u32]) == Some(1u32));
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_minimal_case_finds_one() {
    assert(find_duplicate(seq![1u32, 1u32]) == Some(1u32));
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn test_finds_in_larger_list() {
    assert(find_duplicate(seq![1u32, 2u32, 3u32, 4u32, 5u32, 6u32, 7u32, 8u32, 9u32, 5u32]) == Some(5u32));
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // let result1 = find_duplicate(seq![1u32, 3u32, 4u32, 2u32, 2u32]);
    // println!("{:?}", result1);
    
    // let result2 = find_duplicate(seq![3u32, 1u32, 3u32, 4u32, 2u32]);
    // println!("{:?}", result2);
    
    // let result3 = find_duplicate(seq![2u32, 2u32, 2u32, 2u32, 2u32]);
    // println!("{:?}", result3);
}