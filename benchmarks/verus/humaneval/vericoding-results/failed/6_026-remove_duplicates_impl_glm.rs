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
/* helper modified by LLM (iteration 4): changed to executable function returning usize */
fn count_frequency(v: &Vec<i64>, key: i64) -> (result: usize)
    ensures result as int == count_frequency_spec(v@, key)
{
    let mut count = 0;
    for i in 0..v.len() {
        if v[i] == key {
            count += 1;
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
/* code modified by LLM (iteration 4): use executable count_frequency and compare with usize 1 */
{
    let mut result = Vec::new();
    for i in 0..numbers.len() {
        if count_frequency(numbers, numbers[i]) == 1 {
            result.push(numbers[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}