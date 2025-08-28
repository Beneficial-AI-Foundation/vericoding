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
        decreases arr.len() - index
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

proof fn lemma_count_frequency_take(seq: Seq<char>, i: int, key: char)
    requires 0 <= i <= seq.len()
    ensures count_frequency_rcr(seq.take(i), key) == count_frequency_rcr(seq.subrange(0, i), key)
    decreases i
{
    if i == 0 {
    } else {
        lemma_count_frequency_take(seq, i - 1, key);
    }
}

proof fn lemma_take_filter_property(str1: Seq<char>, i: int)
    requires 0 <= i <= str1.len()
    requires forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1, #[trigger] str1[k]) <= 1
    ensures str1.take(i) =~= str1.take(i).filter(|x: char| count_frequency_rcr(str1, x) <= 1)
    decreases i
{
    if i == 0 {
    } else {
        lemma_take_filter_property(str1, i - 1);
        assert(str1[i - 1] == str1.take(i).last());
        assert(count_frequency_rcr(str1, str1[i - 1]) <= 1);
    }
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
{
    let mut i = 0;
    while i < str1.len()
        invariant {
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1@[k]) <= 1,
        }
        decreases str1.len() - i
    {
        let ch = str1[i];
        let freq = count_frequency(str1, ch);
        if freq > 1 {
            proof {
                lemma_count_frequency_take(str1@, i as int, ch);
                lemma_take_filter_property(str1@, i as int);
            }
            return Some((i, ch));
        }
        i += 1;
    }
    None
}
// </vc-code>

} // verus!

fn main() {}