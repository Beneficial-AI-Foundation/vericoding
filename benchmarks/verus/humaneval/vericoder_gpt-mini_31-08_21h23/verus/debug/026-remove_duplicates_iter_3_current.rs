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
fn vec_of_seq(s: Seq<i64>) -> Vec<i64>
    ensures
        result@ == s,
    decreases
        s.len()
{
    if s.len() == 0 {
        Vec::new()
    } else {
        let mut v = vec_of_seq(s.drop_last());
        v.push(s.last());
        v
    }
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
    let seq: Seq<i64> = numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1);
    vec_of_seq(seq)
}
// </vc-code>

} // verus!
fn main() {}