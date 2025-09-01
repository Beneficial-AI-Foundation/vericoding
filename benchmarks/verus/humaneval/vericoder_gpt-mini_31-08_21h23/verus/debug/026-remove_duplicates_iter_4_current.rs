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
    let seq: Seq<i64> = numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1);
    let mut v: Vec<i64> = Vec::new();
    let mut i: nat = 0;
    while i < seq.len()
        invariant i <= seq.len();
        invariant v.len() == i;
        invariant v@ == seq.slice(0, i);
        decreases seq.len() - i
    {
        v.push(seq[i]);
        i = i + 1;
    }
    v
}
// </vc-code>

} // verus!
fn main() {}