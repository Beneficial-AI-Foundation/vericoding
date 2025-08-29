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
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        decreases arr.len() - index,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}

proof fn lemma_count_frequency_monotonic(seq: Seq<char>, key: char)
    ensures
        forall|i: int, j: int| 0 <= i <= j <= seq.len() ==>
            count_frequency_rcr(seq.subrange(0, i), key) <= count_frequency_rcr(seq.subrange(0, j), key)
    decreases seq.len()
{
    /* code modified by LLM (iteration 5): converted to spec function with decreases and removed proof block */
    lemma_count_frequency_monotonic_inductive(seq, key, seq.len());
}

proof fn lemma_count_frequency_monotonic_inductive(seq: Seq<char>, key: char, n: int)
    requires 0 <= n <= seq.len()
    ensures forall|i: int, j: int| 0 <= i <= j <= n ==>
        count_frequency_rcr(seq.subrange(0, i), key) <= count_frequency_rcr(seq.subrange(0, j), key)
    decreases n
{
    if n == 0 {
        assert forall|i: int, j: int| 0 <= i <= j <= 0 implies i == 0 && j == 0 by {};
    } else {
        lemma_count_frequency_monotonic_inductive(seq, key, n - 1);
        assert forall|i: int, j: int| 0 <= i <= j <= n implies
            count_frequency_rcr(seq.subrange(0, i), key) <= count_frequency_rcr(seq.subrange(0, j), key) by {
            if 0 <= i <= j <= n {
                if j < n {
                } else {
                    assert(j == n);
                    if i < n {
                        assert(count_frequency_rcr(seq.subrange(0, n), key) == 
                               count_frequency_rcr(seq.subrange(0, n - 1), key) + 
                               if seq[n - 1] == key { 1int } else { 0int });
                    }
                }
            }
        };
    }
}

proof fn lemma_count_frequency_prefix(seq: Seq<char>, key: char, i: int, j: int)
    requires 0 <= i < j <= seq.len()
    ensures count_frequency_rcr(seq.subrange(0, j), key) >= count_frequency_rcr(seq.subrange(0, i), key)
{
    /* code modified by LLM (iteration 3): added proof using monotonicity lemma */
    lemma_count_frequency_monotonic(seq, key);
    assert(0 <= i <= j <= seq.len());
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
    /* code modified by LLM (iteration 3): strengthened invariant and added assertions to prove postcondition */
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@.take(i as int), #[trigger] str1[k]) <= 1,
        decreases str1.len() - i,
    {
        let freq = count_frequency(str1, str1[i]);
        if freq > 1 {
            /* code modified by LLM (iteration 5): removed proof block and moved assertions outside */
            assert(count_frequency_rcr(str1@, str1@[i as int]) > 1);
            assert forall|k: int| 0 <= k < i implies count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1 by {};
            assert(str1@.take(i as int) =~= str1@.take(i as int).filter(
                |x: char| count_frequency_rcr(str1@, x) <= 1
            )) by {
                assert forall|idx: int| 0 <= idx < i implies {
                    let ch = str1[idx];
                    count_frequency_rcr(str1@, ch) <= 1
                } by {};
            };
            return Some((i, str1[i]));
        }
        i += 1;
    }
    None
}
// </vc-code>

} // verus!

fn main() {}