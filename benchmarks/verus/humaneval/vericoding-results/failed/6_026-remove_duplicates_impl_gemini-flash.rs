// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in this turn. */
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Dereferenced `current_num` and `num` to match expected `i64` type for `contains`, `insert`, and `remove` methods of `Set` and `Vec`, and `count_frequency_spec` function. */
{
    let mut unique_numbers_set: Set<i64> = Set::empty();
    let mut duplicate_numbers_set: Set<i64> = Set::empty();

    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            forall|j: int| 0 <= j && (j as usize) < i ==> {
                let current_num = *numbers.get(j as usize).unwrap();
                if unique_numbers_set.contains(current_num) {
                    !duplicate_numbers_set.contains(current_num)
                } else if duplicate_numbers_set.contains(current_num) {
                    !unique_numbers_set.contains(current_num)
                } else {
                    true // current_num is neither in unique_numbers_set nor duplicate_numbers_set yet
                }
            },
            // All elements processed so far are correctly categorized into unique_numbers_set or duplicate_numbers_set
            forall |k: int| 0 <= k && (k as usize) < i && duplicate_numbers_set.contains(*numbers.get(k as usize).unwrap()) ==> {
                let sub_seq = numbers@.take(i as int);
                let count = count_frequency_spec(sub_seq, *numbers.get(k as usize).unwrap());
                count >= 2
            },
            forall |k: int| 0 <= k && (k as usize) < i && unique_numbers_set.contains(*numbers.get(k as usize).unwrap()) ==> {
                let sub_seq = numbers@.take(i as int);
                let count = count_frequency_spec(sub_seq, *numbers.get(k as usize).unwrap());
                count == 1
            },
        decreases numbers.len() - i
    {
        let num = numbers.get(i).unwrap();
        if unique_numbers_set.contains(*num) {
            unique_numbers_set = unique_numbers_set.remove(*num);
            duplicate_numbers_set = duplicate_numbers_set.insert(*num);
        } else if !duplicate_numbers_set.contains(*num) {
            unique_numbers_set = unique_numbers_set.insert(*num);
        }
        i = i + 1;
    }

    let mut final_unique_vec: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    let mut k: usize = 0;
    while j < numbers.len()
        invariant
            0 <= j && j <= numbers.len(),
            k == final_unique_vec.len(),
            forall|idx: int| 0 <= idx && (idx as usize) < k ==> {
                let val = *final_unique_vec.get(idx as usize).unwrap();
                unique_numbers_set.contains(val)
            },
            final_unique_vec.len() == k,
            forall|idx: int| 0 <= idx && (idx as usize) < j ==> {
                if unique_numbers_set.contains(*numbers.get(idx as usize).unwrap()) && !duplicate_numbers_set.contains(*numbers.get(idx as usize).unwrap()) {
                    final_unique_vec@.contains(*numbers.get(idx as usize).unwrap())
                } else {
                    !final_unique_vec@.contains(*numbers.get(idx as usize).unwrap())
                }
            },
            forall |x: i64| final_unique_vec@.contains(x) ==> numbers@.contains(x),
            forall |x: i64| numbers@.contains(x) && unique_numbers_set.contains(x) && !duplicate_numbers_set.contains(x) ==> final_unique_vec@.contains(x),
        decreases numbers.len() - j
    {
        let num = numbers.get(j).unwrap();
        if unique_numbers_set.contains(*num) && !duplicate_numbers_set.contains(*num) {
            final_unique_vec.push(*num);
            k = k + 1;
        }
        j = j + 1;
    }

    proof {
        assert(final_unique_vec@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == (1 as int)));
    }
    final_unique_vec
}
// </vc-code>

}
fn main() {}