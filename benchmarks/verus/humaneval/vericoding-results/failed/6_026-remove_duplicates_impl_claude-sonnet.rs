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
spec fn is_unique_in_seq(seq: Seq<i64>, x: i64) -> bool {
    count_frequency_spec(seq, x) == 1
}

proof fn count_frequency_empty(key: i64)
    ensures count_frequency_spec(Seq::<i64>::empty(), key) == 0
{
}

proof fn count_frequency_single(x: i64, key: i64)
    ensures count_frequency_spec(seq![x], key) == if x == key { 1 } else { 0 }
{
}

proof fn count_frequency_push(seq: Seq<i64>, x: i64, key: i64)
    ensures count_frequency_spec(seq.push(x), key) == count_frequency_spec(seq, key) + if x == key { 1 } else { 0 }
{
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed invalid 'int' suffix from integer literals */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let current = numbers[i];
        if count_frequency_spec(numbers@, current) == 1 {
            result.push(current);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}