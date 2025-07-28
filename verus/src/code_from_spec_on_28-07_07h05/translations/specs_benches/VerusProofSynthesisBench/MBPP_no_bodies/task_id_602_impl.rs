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
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count_frequency_rcr(arr@.take(i as int), key) == count,
            count <= arr.len(),
        decreases arr.len() - i,
    {
        if arr[i] == key {
            /* code modified by LLM (iteration 1): moved lemma call inside proof block */
            proof {
                lemma_count_frequency_extend(arr@, i as int, key);
            }
            count = count + 1;
        } else {
            /* code modified by LLM (iteration 1): moved lemma call inside proof block */
            proof {
                lemma_count_frequency_extend(arr@, i as int, key);
            }
        }
        i = i + 1;
    }
    
    assert(arr@.take(arr.len() as int) =~= arr@);
    count
}

proof fn lemma_count_frequency_extend(seq: Seq<char>, i: int, key: char)
    requires 0 <= i < seq.len()
    ensures count_frequency_rcr(seq.take(i + 1), key) == 
            count_frequency_rcr(seq.take(i), key) + if seq[i] == key { 1 } else { 0 }
    decreases seq.len() - i
{
    if i == 0 {
        assert(seq.take(1) =~= seq![seq[0]]);
        assert(seq.take(0) =~= seq![]);
    } else {
        let seq_i = seq.take(i);
        let seq_i_plus_1 = seq.take(i + 1);
        assert(seq_i_plus_1 =~= seq_i.push(seq[i]));
        
        // Use the recursive definition
        assert(count_frequency_rcr(seq_i_plus_1, key) == 
               count_frequency_rcr(seq_i_plus_1.drop_last(), key) + 
               if seq_i_plus_1.last() == key { 1 } else { 0 });
        assert(seq_i_plus_1.drop_last() =~= seq_i);
        assert(seq_i_plus_1.last() == seq[i]);
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
// pure-end

fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    // post-conditions-start
    ensures
        check_first_repeated_char(str1, repeated_char),
    // post-conditions-end
{
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
            str1@.take(i as int) =~= str1@.take(i as int).filter(
                |x: char| count_frequency_rcr(str1@, x) <= 1,
            ),
        decreases str1.len() - i,
    {
        let char_at_i = str1[i];
        let freq = count_frequency(str1, char_at_i);
        
        if freq > 1 {
            return Some((i, char_at_i));
        }
        
        proof {
            let new_take = str1@.take((i + 1) as int);
            let old_take = str1@.take(i as int);
            assert(new_take =~= old_take.push(char_at_i));
            
            // Show that the new take is equal to its filter
            assert(forall|x: char| new_take.contains(x) && count_frequency_rcr(str1@, x) <= 1 
                   ==> old_take.contains(x) || x == char_at_i);
            assert(count_frequency_rcr(str1@, char_at_i) <= 1);
            
            lemma_filter_extend(old_take, char_at_i, |x: char| count_frequency_rcr(str1@, x) <= 1);
        }
        
        i = i + 1;
    }
    
    None
}

proof fn lemma_filter_extend<T>(seq: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    requires pred(elem)
    ensures seq.push(elem).filter(pred) =~= seq.filter(pred).push(elem)
{
    let new_seq = seq.push(elem);
    let filtered_new = new_seq.filter(pred);
    let filtered_old = seq.filter(pred);
    
    // The proof follows from the definition of filter
    assert(filtered_new =~= filtered_old.push(elem));
}

} // verus!

fn main() {}