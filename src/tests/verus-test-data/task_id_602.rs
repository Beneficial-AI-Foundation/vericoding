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

fn count_frequency(arr: &Vec<char>, key: char) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_rcr(arr@, key) == frequency,
    // post-conditions-end
{
    // impl-start
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        // invariants-start
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        // invariants-end
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        // assert-start
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
        // assert-end
    }
    // assert-start
    assert(arr@ == arr@.subrange(0, index as int));
    // assert-end
    counter
    // impl-end
}

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

fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    // post-conditions-start
    ensures
        check_first_repeated_char(str1, repeated_char),
    // post-conditions-end
{
    // impl-start
    let input_len = str1.len();
    // assert-start
    assert(str1@.take(0int).filter(|x: char| count_frequency_rcr(str1@, x) > 1) == Seq::<
        char,
    >::empty());
    // assert-end
    let mut index = 0;
    while index < str1.len()
        // invariants-start
        invariant
            0 <= index <= str1.len(),
            str1@.take(index as int) =~= str1@.take(index as int).filter(
                |x: char| count_frequency_rcr(str1@, x) <= 1,
            ),
        // invariants-end
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        // assert-start
        assert(str1@.take((index + 1) as int).drop_last() == str1@.take(index as int));
        reveal(Seq::filter);
        // assert-end
        index += 1;
    }
    // assert-start
    assert(str1@ =~= str1@.take(input_len as int));
    assert(forall|k: int|
        0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1);
    // assert-end
    None
    // impl-end
}

} // verus!

fn main() {}
