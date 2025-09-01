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
    // impl-start
    let mut unique_numbers: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            unique_numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1).len() == unique_numbers.len(), // Added more specific invariant 
            forall|j: int| 0 <= j < unique_numbers.len() ==> count_frequency_spec(numbers@.subsequence(0, i as int), unique_numbers@[j]) == 1,
            forall|j: int| 0 <= j < unique_numbers.len() ==> unique_numbers@[j] == unique_numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1)@.contains(unique_numbers@[j]),
            forall|j: int| 0 <= j < i ==> 
                (count_frequency_spec(numbers@, numbers@[j]) == 1) == unique_numbers@.contains(numbers@[j]),
            forall|k: int| 0 <= k < unique_numbers.len() && unique_numbers@.contains(numbers@[i]) && count_frequency_spec(numbers@, unique_numbers@[k]) == 1 && count_frequency_spec(numbers@, numbers@[i]) == 1 ==> unique_numbers@[k] != numbers@[i] || k == unique_numbers.len() - 1,

    {
        let num = numbers@[i];
        if count_frequency_spec(numbers@, num) == 1 {
            unique_numbers.push(num);
        }
        i = i + 1;
    }
    unique_numbers
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}