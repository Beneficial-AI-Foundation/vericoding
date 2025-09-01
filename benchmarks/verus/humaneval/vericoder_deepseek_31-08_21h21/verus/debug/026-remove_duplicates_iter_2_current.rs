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

proof fn lemma_count_frequency_filter<F: Fn(i64) -> bool>(seq: Seq<i64>, key: i64, f: F)
    ensures
        count_frequency_spec(seq.filter(f), key) == if f(key) { count_frequency_spec(seq, key) } else { 0 },
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        lemma_count_frequency_filter(seq.drop_last(), key, f);
    }
}

proof fn lemma_count_frequency_positive(seq: Seq<i64>, key: i64)
    ensures
        count_frequency_spec(seq, key) >= 0,
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        lemma_count_frequency_positive(seq.drop_last(), key);
    }
}

spec fn is_unique_in_seq(seq: Seq<i64>, x: i64) -> bool {
    count_frequency_spec(seq, x) == 1
}

proof fn lemma_count_frequency_subrange(seq: Seq<i64>, start: int, end: int, key: i64)
    requires
        0 <= start <= end <= seq.len(),
    ensures
        count_frequency_spec(seq.subrange(start, end), key) == count_frequency_spec(seq, key) - count_frequency_spec(seq.subrange(0, start), key) - count_frequency_spec(seq.subrange(end, seq.len()), key),
    decreases end - start,
{
    if start >= end {
    } else {
        lemma_count_frequency_subrange(seq, start + 1, end, key);
    }
}

proof fn lemma_count_frequency_consistency(seq: Seq<i64>, subseq: Seq<i64>, key: i64)
    requires
        subseq =~= seq.subrange(0, seq.len()),
    ensures
        count_frequency_spec(seq, key) == count_frequency_spec(subseq, key),
{
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
    let mut unique_numbers: Vec<i64> = Vec::new();
    let mut seen: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            seen@.len() == i,
            seen@ =~= numbers@.subrange(0, i),
            unique_numbers@ == numbers@.subrange(0, i).filter(|x: i64| count_frequency_spec(numbers@.subrange(0, i), x) == 1),
        decreases numbers.len() - i,
    {
        let current = numbers[i];
        let mut count: usize = 0;
        let mut j: usize = 0;
        
        while j < i
            invariant
                0 <= j <= i,
                count == count_frequency_spec(seen@.subrange(0, j), current) as usize,
            decreases i - j,
        {
            if seen[j] == current {
                count = count + 1;
            }
            j = j + 1;
        }
        
        if count == 0 {
            let mut k: usize = i + 1;
            let mut future_count: usize = 0;
            
            while k < numbers.len()
                invariant
                    i < k <= numbers.len(),
                    future_count == count_frequency_spec(numbers@.subrange(i + 1, k), current) as usize,
                decreases numbers.len() - k,
            {
                if numbers[k] == current {
                    future_count = future_count + 1;
                }
                k = k + 1;
            }
            
            if future_count == 0 {
                unique_numbers.push(current);
            }
        }
        
        seen.push(current);
        i = i + 1;
    }
    
    proof {
        lemma_count_frequency_filter(numbers@, current, |x| is_unique_in_seq(numbers@, x));
        assert(unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1));
    }
    
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}