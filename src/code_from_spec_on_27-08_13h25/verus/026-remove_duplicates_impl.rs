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
fn count_frequency(elements: &Vec<i64>, key: i64) -> (frequency: usize)
    ensures
        count_frequency_spec(elements@, key) == frequency,
{
    let ghost elements_length = elements.len();
    let mut counter = 0;
    let mut index = 0;
    while index < elements.len()
        invariant
            0 <= index <= elements.len(),
            0 <= counter <= index,
            count_frequency_spec(elements@.subrange(0, index as int), key) == counter,
        decreases elements.len() - index,
    {
        if elements[index] == key {
            counter += 1;
        }
        index += 1;
        assert(elements@.subrange(0, index - 1 as int) == elements@.subrange(0, index as int).drop_last());
    }
    assert(elements@ == elements@.subrange(0, elements_length as int));
    counter
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
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result@.len() <= i,
            forall |j: int| 0 <= j < result@.len() ==> count_frequency_spec(numbers@, result@[j]) == 1,
            forall |j: int| 0 <= j < i ==> 
                count_frequency_spec(numbers@, numbers@[j]) > 1 ==> 
                !result@.contains(numbers@[j]),
        decreases numbers.len() - i,
    {
        let freq = count_frequency(numbers, numbers[i]);
        if freq == 1 {
            result.push(numbers[i]);
        }
        i += 1;
    }
    proof {
        assert(forall |x: i64| result@.contains(x) ==> count_frequency_spec(numbers@, x) == 1) by {
            assert forall |j: int| 0 <= j < result@.len() implies count_frequency_spec(numbers@, result@[j]) == 1 by {
                if 0 <= j < result@.len() {
                    assert(count_frequency_spec(numbers@, result@[j]) == 1);
                }
            };
        };
        assert(forall |x: i64| count_frequency_spec(numbers@, x) == 1 ==> result@.contains(x)) by {
            assert forall |j: int| 0 <= j < numbers@.len() implies 
                (count_frequency_spec(numbers@, numbers@[j]) == 1 ==> result@.contains(numbers@[j])) by {
                if 0 <= j < numbers@.len() && count_frequency_spec(numbers@, numbers@[j]) == 1 {
                    assert(result@.contains(numbers@[j]));
                }
            };
        };
    }
    result
}
// </vc-code>

} // verus!
fn main() {}