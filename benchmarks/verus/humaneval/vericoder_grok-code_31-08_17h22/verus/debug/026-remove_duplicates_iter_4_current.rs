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
spec fn count_frequency(seq: Seq<i64>, key: i64) -> (result: int)
    ensures
        result == count_frequency_spec(seq, key),
{
    let mut count = 0;
    let mut i: int = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            count == count_frequency_spec(seq.take(i as int), key),
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
    // post-conditions-start
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let seq = numbers@;
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result@ == seq.take(i as int).filter(|x: i64| count_frequency_spec(seq, x) == 1),
    {
        let current = numbers[i];
        if count_frequency(seq, current) == 1 {
            result.push(current);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}