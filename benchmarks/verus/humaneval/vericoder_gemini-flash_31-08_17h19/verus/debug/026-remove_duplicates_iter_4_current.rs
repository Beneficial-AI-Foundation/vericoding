use vstd::prelude::*;

verus! {

spec fn count_frequency_spec(seq: Seq<i64>, key: i64) -> (result:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_spec(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
// removed the duplicate function definition: spec fn count_frequency_spec ...
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    // post-conditions-start
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut unique_numbers: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            // Ensure unique_numbers only contains elements from the original `numbers` that appear exactly once in `numbers`
            forall|j: int| 0 <= j < unique_numbers.len() ==> {
                &&& numbers@.contains(unique_numbers@[j])
                &&& count_frequency_spec(numbers@, unique_numbers@[j]) == 1
            },
            // All elements processed up to `i` that appear exactly once in `numbers` are in `unique_numbers`
            forall|j: int| 0 <= j < i ==> {
                let num_j = numbers@[j as int];
                (count_frequency_spec(numbers@, num_j) == 1) == unique_numbers@.contains(num_j)
            },
            // All elements in `unique_numbers` are distinct
            forall|j: int, k: int| 0 <= j < k < unique_numbers.len() ==> unique_numbers@[j] != unique_numbers@[k],
    {
        let num = numbers.view_native()[i]; // changed to view_native() to use i as usize
        if count_frequency_spec(numbers@, num) == 1 {
            let old_len = unique_numbers.len();
            unique_numbers.push(num);
            proof {
                assert(unique_numbers.len() == old_len + 1);
            }
        }
        i = i + 1;
    }
    unique_numbers
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}