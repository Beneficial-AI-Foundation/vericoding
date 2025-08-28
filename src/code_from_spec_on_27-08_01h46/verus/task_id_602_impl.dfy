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
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}

proof fn lemma_count_frequency_prefix_property(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures forall|k: int| 0 <= k <= i ==> count_frequency_rcr(s.take(i), s[k]) <= count_frequency_rcr(s, s[k])
{
    let prefix = s.take(i);
    assert(prefix.len() <= s.len());
    
    assert forall|k: int| 0 <= k <= i implies count_frequency_rcr(s.take(i), s[k]) <= count_frequency_rcr(s, s[k]) by {
        if 0 <= k <= i {
            let c = s[k];
            let prefix_count = count_frequency_rcr(prefix, c);
            let full_count = count_frequency_rcr(s, c);
            
            assert(prefix_count <= full_count) by {
                lemma_count_frequency_monotonic(s, i, c);
            }
        }
    }
}

proof fn lemma_count_frequency_take_property(s: Seq<char>, i: int, c: char)
    requires 0 <= i < s.len()
    ensures count_frequency_rcr(s.take(i), c) + (if s[i] == c { 1int } else { 0int }) <= count_frequency_rcr(s, c)
{
    let prefix_count = count_frequency_rcr(s.take(i), c);
    let additional = if s[i] == c { 1int } else { 0int };
    let total_count = count_frequency_rcr(s, c);
    
    lemma_count_frequency_monotonic(s, i, c);
    
    if s[i] == c {
        assert(count_frequency_rcr(s.take(i + 1), c) == prefix_count + 1);
        assert(count_frequency_rcr(s.take(i + 1), c) <= total_count) by {
            lemma_count_frequency_monotonic(s, i + 1, c);
        }
        assert(prefix_count + 1 <= total_count);
    } else {
        assert(count_frequency_rcr(s.take(i + 1), c) == prefix_count);
        assert(prefix_count <= total_count);
    }
}

proof fn lemma_count_frequency_monotonic(s: Seq<char>, i: int, c: char)
    requires 0 <= i <= s.len()
    ensures count_frequency_rcr(s.take(i), c) <= count_frequency_rcr(s, c)
    decreases s.len() - i
{
    if i == s.len() {
        assert(s.take(i) == s);
    } else {
        let prefix = s.take(i);
        let extended = s.take(i + 1);
        
        if s.len() > 0 {
            if s[s.len() - 1] == c {
                assert(count_frequency_rcr(s, c) == count_frequency_rcr(s.drop_last(), c) + 1);
            } else {
                assert(count_frequency_rcr(s, c) == count_frequency_rcr(s.drop_last(), c));
            }
        }
        
        if i < s.len() {
            lemma_count_frequency_monotonic(s, i + 1, c);
        }
    }
}

proof fn lemma_filter_property(s: Seq<char>, i: int)
    requires 0 <= i <= s.len()
    requires forall|k: int| 0 <= k < i ==> count_frequency_rcr(s, s[k]) <= 1
    ensures s.take(i) =~= s.take(i).filter(|x: char| count_frequency_rcr(s, x) <= 1)
{
    let prefix = s.take(i);
    let filtered = prefix.filter(|x: char| count_frequency_rcr(s, x) <= 1);
    
    assert(prefix.len() == filtered.len()) by {
        assert forall|j: int| 0 <= j < prefix.len() implies count_frequency_rcr(s, prefix[j]) <= 1 by {
            if 0 <= j < prefix.len() {
                assert(j < i);
                assert(prefix[j] == s[j]);
                assert(count_frequency_rcr(s, s[j]) <= 1);
            }
        }
    }
    
    assert forall|j: int| 0 <= j < prefix.len() implies prefix[j] == filtered[j] by {
        if 0 <= j < prefix.len() {
            assert(count_frequency_rcr(s, prefix[j]) <= 1);
        }
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
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, str1@[k]) <= 1,
        decreases str1.len() - i,
    {
        let freq = count_frequency(str1, str1[i]);
        if freq > 1 {
            proof {
                lemma_count_frequency_prefix_property(str1@, i as int);
                lemma_count_frequency_take_property(str1@, i as int, str1@[i as int]);
                assert(forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, str1@[k]) <= 1);
                assert(count_frequency_rcr(str1@, str1@[i as int]) > 1);
                lemma_filter_property(str1@, i as int);
            }
            return Some((i, str1[i]));
        }
        i += 1;
    }
    None
}
// </vc-code>

} // verus!

fn main() {}