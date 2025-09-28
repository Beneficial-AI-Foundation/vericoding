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
/* helper modified by LLM (iteration 5): Added missing lemma definitions */
proof fn lemma_count_frequency_take(seq: Seq<char>, c: char, n: int)
    requires 0 <= n <= seq.len()
    ensures count_frequency_rcr(seq.take(n), c) <= count_frequency_rcr(seq, c)
    decreases n
{
    if n == 0 {
        assert(seq.take(0) =~= Seq::<char>::empty());
    } else {
        assert(seq.take(n) =~= seq.take(n - 1).push(seq[n - 1]));
        lemma_count_frequency_take(seq, c, n - 1);
    }
}

proof fn lemma_count_frequency_extend(seq: Seq<char>, elem: char, new_elem: char)
    ensures count_frequency_rcr(seq.push(new_elem), elem) == 
            count_frequency_rcr(seq, elem) + if elem == new_elem { 1 } else { 0 }
    decreases seq.len()
{
    assert(seq.push(new_elem).drop_last() =~= seq);
    assert(seq.push(new_elem).last() == new_elem);
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed proof logic with proper lemma calls */
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant
            i <= str1.len(),
            forall|j: int| 0 <= j < i ==> count_frequency_rcr(str1@.take(i as int), str1@[j]) <= 1,
        decreases str1.len() - i
    {
        let c = str1[i];
        let mut j: usize = 0;
        
        while j < i
            invariant
                j <= i,
                i < str1.len(),
                c == str1@[i as int],
            decreases i - j
        {
            if str1[j] == c {
                proof {
                    lemma_count_frequency_take(str1@, c, (i + 1) as int);
                    assert(count_frequency_rcr(str1@, c) >= 2);
                }
                return Some((j, c));
            }
            j = j + 1;
        }
        
        i = i + 1;
        
        proof {
            assert(str1@.take(i as int) =~= str1@.take((i - 1) as int).push(c));
            assert forall|k: int| 0 <= k < i as int implies count_frequency_rcr(str1@.take(i as int), str1@[k]) <= 1 by {
                if k < (i - 1) as int {
                    lemma_count_frequency_extend(str1@.take((i - 1) as int), str1@[k], c);
                    assert(str1@[k] != c);
                } else {
                    assert(k == (i - 1) as int);
                    assert(str1@[k] == c);
                    lemma_count_frequency_extend(str1@.take((i - 1) as int), c, c);
                }
            }
        }
    }
    
    None
}
// </vc-code>

}
fn main() {}