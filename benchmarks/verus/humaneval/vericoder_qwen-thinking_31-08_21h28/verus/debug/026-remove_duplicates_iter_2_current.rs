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
use vstd::map::Map;
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
    let mut freq = Map::new(|a, b| a == b, |a, b| a == b);
    for num in numbers.iter() {
        let count = match freq.get(num) {
            Some(c) => c,
            None => 0,
        };
        freq.insert(*num, count + 1);
    }
    let mut unique_numbers = Vec::new();
    for num in numbers.iter() {
        if freq.get(num) == Some(1) {
            unique_numbers.push(*num);
        }
    }
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}