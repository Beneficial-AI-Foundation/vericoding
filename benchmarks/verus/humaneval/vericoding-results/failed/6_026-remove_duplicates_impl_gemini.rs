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
/* helper modified by LLM (iteration 5): No functional change, helper is correct. */
fn count_frequency_exec(seq: &Vec<i64>, key: i64) -> (count: i64)
    ensures
        count == count_frequency_spec(seq@, key),
{
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < seq.len()
        invariant
            i <= seq.len(),
            count == count_frequency_spec(seq@.subrange(0, i as int), key),
        decreases seq.len() - i
    {
        if seq[i] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected the path and name of the proof lemma to fix a compilation error. */
    let mut unique_numbers = Vec::new();
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            unique_numbers@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
        decreases numbers.len() - i
    {
        let current_number = numbers[i];
        let count = count_frequency_exec(numbers, current_number);
        if count == 1 {
            unique_numbers.push(current_number);
        }
        
        proof {
            let pred = |x: i64| count_frequency_spec(numbers@, x) == 1;
            vstd::seq::lemma_filter_push_distrib(numbers@.subrange(0, i as int), pred, numbers@[i]);
        }

        i = i + 1;
    }
    unique_numbers
}
// </vc-code>

}
fn main() {}