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
/* helper modified by LLM (iteration 5): Fix arithmetic overflow by using nat type for count */
fn count_frequency(vec: &Vec<i64>, key: i64) -> (count: nat)
    ensures count == count_frequency_spec(vec@, key),
{
    let mut count: nat = 0;
    for j in 0..vec.len()
        invariant count == count_frequency_spec(vec@.subrange(0, j as int), key),
    {
        if vec[j] == key {
            count = count + 1;
        }
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
/* code modified by LLM (iteration 5): Fix index bounds by using proper usize casting */
{
    let mut freqs: Vec<u64> = Vec::new();
    for i in 0..numbers.len()
        invariant
            freqs.len() == i,
            forall|k: int| 0 <= k < i ==> freqs@[k] as int == count_frequency_spec(numbers@, numbers@[k]),
    {
        let freq = count_frequency(numbers, numbers[i]);
        freqs.push(freq);
    }

    let mut result = Vec::new();
    for i in 0..numbers.len()
        invariant
            result@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        if freqs[i as usize] == 1 {
            result.push(numbers[i]);
        }
    }

    result
}
// </vc-code>

}
fn main() {}