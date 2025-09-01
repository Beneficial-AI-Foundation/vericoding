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
fn count_in_seq(seq: &Vec<i64>, key: i64) -> (res: u32) 
    ensures
        res as int == count_frequency_spec((*seq)@, key)
{
    let mut cnt: u32 = 0;
    let mut i: usize = 0;
    while i < seq.len()
        decreases (seq.len() - i)
        invariant
            cnt as int == count_frequency_spec(seq@.subrange(0, i as nat), key)
    {
        if seq[i] == key {
            cnt += 1;
        }
        i += 1;
    }
    cnt
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
    let mut i: usize = 0;
    while i < numbers.len()
        decreases (numbers.len() - i)
        invariant
            result@ == numbers@.subrange(0, i as nat).filter(|x: i64| count_frequency_spec(numbers@, x) == 1)
    {
        let num = numbers[i];
        if count_in_seq(&numbers, num) == 1 {
            result.push(num);
        }
        i += 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}