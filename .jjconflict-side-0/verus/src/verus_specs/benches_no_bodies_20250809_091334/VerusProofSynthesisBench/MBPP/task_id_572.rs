use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_rcr(arr@, key) == frequency,
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
