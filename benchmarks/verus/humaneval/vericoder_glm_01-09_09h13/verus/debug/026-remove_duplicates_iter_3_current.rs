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
proof fn lemma_count_frequency_drop_last<Q: Integer>(seq: Seq<i64>, key: i64, x: Q)
    requires
        0 <= x < seq.len(),
    ensures
        count_frequency_spec(seq, key) == count_frequency_spec(seq.drop_last(), key) + if seq.last() == key { 1 } else { 0 },
{
    reveal(count_frequency_spec);
}

proof fn lemma_count_frequency_preserved(seq: Seq<i64>, new_seq: Seq<i64>, key: i64)
    requires
        seq.len() == new_seq.len(),
        forall|i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] == new_seq[i],
    ensures
        count_frequency_spec(seq, key) == count_frequency_spec(new_seq, key),
{
    assert(seq == new_seq);
    reveal(count_frequency_spec);
}

proof fn lemma_filter_frequency_is_singleton(s: Seq<i64>, key: i64)
    ensures
        (s.filter(|x: i64| count_frequency_spec(s, x) == 1)).contains(key) <==> (count_frequency_spec(s, key) == 1),
{
    reveal(count_frequency_spec);
}

proof fn lemma_remove_duplicates_unique_preserved(seq: Seq<i64>, elem: i64)
    ensures
        count_frequency_spec(seq.filter(|x: i64| count_frequency_spec(seq, x) == 1), elem) <= (if count_frequency_spec(seq, elem) == 1 { 1int } else { 0int })
{
    reveal(count_frequency_spec);
}

proof fn lemma_remove_duplicates_freq_zero_if_not_unique(seq: Seq<i64>, elem: i64)
    requires
        count_frequency_spec(seq, elem) != 1,
    ensures
        count_frequency_spec(seq.filter(|x: i64| count_frequency_spec(seq, x) == 1), elem) == 0,
{
    reveal(count_frequency_spec);
}

proof fn lemma_filter_split<A, P: (A) -> bool>(s1: Seq<A>, s2: Seq<A>)
    ensures
        (s1 + s2).filter(P) == s1.filter(P) + s2.filter(P),
{
    assert(forall|s1, s2| (s1 + s2).filter(P) == s1.filter(P) + s2.filter(P));
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
    let mut result_vec: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result_vec@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let key = numbers@[i];
        if count_frequency_spec(numbers@, key) == 1 {
            result_vec.push(key);
        }
        i = i + 1;
        
        proof {
            lemma_filter_split(
                numbers@.subrange(0, (i-1) as int),
                numbers@.subrange((i-1) as int, i as int)
            );
        }
    }
    result_vec
}
// </vc-code>

} // verus!
fn main() {}