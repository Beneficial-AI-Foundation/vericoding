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
// Helper lemma to show that count_frequency_spec counts all occurrences
proof fn count_frequency_spec_properties(seq: Seq<i64>, key: i64, i: int)
    requires 0 <= i <= seq.len(),
    ensures count_frequency_spec(seq.take(i), key) + count_frequency_spec(seq.skip(i), key) == count_frequency_spec(seq, key),
    decreases seq.len() - i,
{
    if i == seq.len() {
        assert(seq.skip(i) =~= Seq::<i64>::empty());
        assert(seq.take(i) =~= seq);
    } else if i == 0 {
        assert(seq.take(i) =~= Seq::<i64>::empty());
        assert(seq.skip(i) =~= seq);
    } else {
        assert(seq.take(i).drop_last() =~= seq.take(i - 1));
        assert(seq.skip(i) =~= seq.skip(i - 1).drop_last());
        count_frequency_spec_properties(seq, key, i - 1);
    }
}

// Helper to show filtering preserves the count relationship
proof fn filter_preserves_single_occurrence(numbers: Seq<i64>, result: Seq<i64>, i: int)
    requires 
        0 <= i <= numbers.len(),
        result == numbers.take(i).filter(|x: i64| count_frequency_spec(numbers, x) == 1),
    ensures
        forall|j: int| 0 <= j < result.len() ==> count_frequency_spec(numbers, result[j]) == 1,
{
    assert forall|j: int| 0 <= j < result.len() implies count_frequency_spec(numbers, result[j]) == 1 by {
        let elem = result[j];
        assert(numbers.take(i).filter(|x: i64| count_frequency_spec(numbers, x) == 1).contains(elem));
    }
}

// Helper to relate count_frequency_spec on take with full sequence
proof fn count_frequency_take_full(seq: Seq<i64>, key: i64, n: int)
    requires 0 <= n <= seq.len(),
    ensures count_frequency_spec(seq.take(n), key) <= count_frequency_spec(seq, key),
    decreases seq.len() - n,
{
    if n == seq.len() {
        assert(seq.take(n) =~= seq);
    } else {
        count_frequency_spec_properties(seq, key, n);
        assert(count_frequency_spec(seq.skip(n), key) >= 0);
    }
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
    let mut unique_numbers = Vec::new();
    let numbers_len = numbers.len();
    
    for i in 0..numbers_len
        invariant
            unique_numbers@ == numbers@.take(i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let current = numbers[i as usize];
        let mut count = 0u64;
        
        // Count occurrences of current element
        for j in 0..numbers_len
            invariant
                0 <= j <= numbers_len,
                count == count_frequency_spec(numbers@.take(j as int), current) as u64,
        {
            if numbers[j as usize] == current {
                count = count + 1;
                
                proof {
                    assert(numbers@.take((j + 1) as int).drop_last() =~= numbers@.take(j as int));
                    assert(numbers@[j as int] == current);
                    assert(count_frequency_spec(numbers@.take((j + 1) as int), current) == 
                           count_frequency_spec(numbers@.take(j as int), current) + 1);
                }
            } else {
                proof {
                    assert(numbers@.take((j + 1) as int).drop_last() =~= numbers@.take(j as int));
                    assert(numbers@[j as int] != current);
                    assert(count_frequency_spec(numbers@.take((j + 1) as int), current) == 
                           count_frequency_spec(numbers@.take(j as int), current));
                }
            }
        }
        
        // Add to result if count is exactly 1
        proof {
            assert(numbers@.take(numbers_len as int) =~= numbers@);
            assert(count == count_frequency_spec(numbers@, current) as u64);
        }
        
        if count == 1 {
            unique_numbers.push(current);
        }
        
        // Prove the main loop invariant
        proof {
            let next_take = numbers@.take((i + 1) as int);
            let curr_take = numbers@.take(i as int);
            
            assert(next_take =~= curr_take.push(current));
            
            let next_filtered = next_take.filter(|x: i64| count_frequency_spec(numbers@, x) == 1);
            let curr_filtered = curr_take.filter(|x: i64| count_frequency_spec(numbers@, x) == 1);
            
            if count == 1 {
                assert(count_frequency_spec(numbers@, current) == 1);
                assert(next_filtered =~= curr_filtered.push(current));
            } else {
                assert(count_frequency_spec(numbers@, current) != 1);
                assert(next_filtered =~= curr_filtered);
            }
        }
    }
    
    proof {
        assert(numbers@.take(numbers_len as int) =~= numbers@);
    }
    
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}