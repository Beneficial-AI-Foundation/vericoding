// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemmas to properly prove postconditions */
proof fn lemma_count_frequency_take(seq: Seq<i64>, key: i64, n: int)
    requires
        0 <= n <= seq.len(),
    ensures
        count_frequency_spec(seq.take(n), key) <= count_frequency_spec(seq, key),
    decreases seq.len() - n
{
    if n == seq.len() {
        assert(seq.take(n) =~= seq);
    } else {
        // seq has more elements after position n
        let tail = seq.drop(n);
        assert(seq =~= seq.take(n) + tail);
        // Count in full seq is count in prefix + count in suffix
        // So count in prefix <= count in full seq
        let elem = seq[seq.len() - 1];
        if elem == key {
            lemma_count_frequency_take(seq.drop_last(), key, n);
        } else {
            lemma_count_frequency_take(seq.drop_last(), key, n);
        }
    }
}

proof fn lemma_count_frequency_push(seq: Seq<i64>, key: i64, elem: i64)
    ensures
        count_frequency_spec(seq.push(elem), key) == count_frequency_spec(seq, key) + if elem == key { 1int } else { 0int },
{
    // By definition of count_frequency_spec
    assert(seq.push(elem).drop_last() =~= seq);
    assert(seq.push(elem).last() == elem);
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed counting logic and invariant maintenance */
    let mut unique_numbers = Vec::new();
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            unique_numbers@ == numbers@.take(i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
            forall|k: int| 0 <= k < unique_numbers.len() ==> count_frequency_spec(numbers@, unique_numbers@[k]) == 1,
        decreases numbers.len() - i
    {
        let current = numbers[i];
        let mut count: nat = 0;
        let mut j: usize = 0;
        
        while j < numbers.len()
            invariant
                0 <= j <= numbers.len(),
                count == count_frequency_spec(numbers@.take(j as int), current) as nat,
                count <= j,
            decreases numbers.len() - j
        {
            if numbers[j] == current {
                proof {
                    lemma_count_frequency_push(numbers@.take(j as int), current, numbers[j]);
                }
                count = count + 1;
            } else {
                proof {
                    lemma_count_frequency_push(numbers@.take(j as int), current, numbers[j]);
                }
            }
            j = j + 1;
        }
        
        proof {
            assert(numbers@.take(numbers.len() as int) =~= numbers@);
        }
        
        if count == 1 {
            unique_numbers.push(current);
            proof {
                // Prove that current appears exactly once in numbers@
                assert(count_frequency_spec(numbers@, current) == 1);
                // The new unique_numbers@ equals the old one plus current
                // And current is in the filter of numbers@.take((i+1) as int)
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(numbers@.take(numbers.len() as int) =~= numbers@);
    }
    
    unique_numbers
}
// </vc-code>

}
fn main() {}