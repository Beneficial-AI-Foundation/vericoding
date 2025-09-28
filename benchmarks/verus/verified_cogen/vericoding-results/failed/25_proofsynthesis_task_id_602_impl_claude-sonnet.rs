// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed count bounds to prevent overflow and fixed proof for take property */
fn count_frequency(seq: &Vec<char>, key: char) -> (result: usize)
    requires
        seq.len() < usize::MAX,
    ensures
        result as int == count_frequency_rcr(seq@, key),
        result <= seq.len(),
{
    let mut count = 0;
    let mut i = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            count as int == count_frequency_rcr(seq@.take(i as int), key),
            count <= i,
        decreases seq.len() - i
    {
        if seq[i] == key {
            count += 1;
        }
        i += 1;
        proof {
            count_frequency_rcr_take_property(seq@, key, i as int);
        }
    }
    count
}

proof fn count_frequency_rcr_take_property(seq: Seq<char>, key: char, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        count_frequency_rcr(seq.take(i), key) == (if i == 0 { 0int } else { count_frequency_rcr(seq.take(i - 1), key) + if seq[i - 1] == key { 1int } else { 0int } }),
{
    if i == 0 {
        assert(seq.take(0) =~= Seq::<char>::empty());
    } else {
        let prev_seq = seq.take(i - 1);
        let curr_seq = seq.take(i);
        assert(curr_seq =~= prev_seq.push(seq[i - 1]));
        assert(count_frequency_rcr(curr_seq, key) == count_frequency_rcr(prev_seq, key) + if seq[i - 1] == key { 1int } else { 0int });
    }
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed slice operation to create new vector properly */
    let mut i = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@.take(k + 1), #[trigger] str1[k]) <= 1,
        decreases str1.len() - i
    {
        let current_char = str1[i];
        let mut prefix = Vec::new();
        let mut j = 0;
        while j <= i
            invariant
                0 <= j <= i + 1,
                prefix.len() == j,
                forall|k: int| 0 <= k < j ==> prefix@[k] == str1@[k],
            decreases i + 1 - j
        {
            prefix.push(str1[j]);
            j += 1;
        }
        
        let freq_in_prefix = count_frequency(&prefix, current_char);
        
        if freq_in_prefix > 1 {
            proof {
                assert(count_frequency_rcr(str1@, current_char) >= freq_in_prefix as int);
                assert(freq_in_prefix > 1);
                assert(count_frequency_rcr(str1@, current_char) > 1);
                
                assert(forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@.take(k + 1), str1[k]) <= 1);
                assert(str1@.take(i as int) =~= str1@.take(i as int).filter(|x: char| count_frequency_rcr(str1@, x) <= 1));
            }
            return Some((i, current_char));
        }
        
        i += 1;
    }
    
    None
}
// </vc-code>

}
fn main() {}