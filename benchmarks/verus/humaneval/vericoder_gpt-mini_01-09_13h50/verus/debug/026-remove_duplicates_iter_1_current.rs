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
// (no helpers needed)
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
    let uniq_seq = numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1);
    let mut unique_numbers: Vec<i64> = Vec::<i64>::new();
    let mut i: nat = 0;
    while i < uniq_seq.len() {
        invariant i <= uniq_seq.len();
        invariant unique_numbers@ == uniq_seq.slice(0, i);
        unique_numbers.push(uniq_seq@[i]);
        i += 1;
    }
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}