use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<char>, key: char) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end
spec fn check_first_repeated_char(str1: &Vec<char>, repeated_char: Option<(usize, char)>) -> (res: bool) {
    if let Some((idx, rp_char)) = repeated_char {
        &&& str1@.take(idx as int) =~= str1@.take(idx as int).filter(
            |x: char| count_frequency_rcr(str1@, x) <= 1,
        )
        &&& count_frequency_rcr(str1@, rp_char) > 1
    } else {
        forall|k: int|
            0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
    }
}
// pure-end

// <vc-helpers>
fn count_frequency(arr: &Vec<char>, key: char) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        decreases arr.len() - index,
    {
        if arr[index] == key {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    // post-conditions-start
    ensures
        check_first_repeated_char(str1, repeated_char),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    ensures
        check_first_repeated_char(str1, repeated_char),
{
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(str1@, str1@[k]) <= 1,
        decreases str1.len() - index,
    {
        let freq = count_frequency(str1, str1@[index]);
        if freq > 1 {
            proof {
                let prefix = str1@.subrange(0, index as int);
                assert(forall|k: int| 0 <= k < index ==> count_frequency_rcr(str1@, str1@[k]) <= 1);
                assert(count_frequency_rcr(str1@, str1@[index]) > 1);
            }
            return Some((index, str1@[index]));
        }
        index += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < str1.len() ==> count_frequency_rcr(str1@, str1@[k]) <= 1);
    }
    None
}
// </vc-code>

} // verus!

fn main() {}