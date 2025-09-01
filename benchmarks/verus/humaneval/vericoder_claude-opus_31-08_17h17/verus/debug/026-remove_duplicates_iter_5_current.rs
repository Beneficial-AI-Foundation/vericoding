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
        // Fixed: use the correct relationship between skip operations
        assert(seq.take(i).drop_last() =~= seq.take(i - 1));
        
        // Key insight: seq.skip(i-1) = seq[i-1] + seq.skip(i)
        let elem_at_i_minus_1 = seq[i - 1];
        assert(seq.skip(i - 1) =~= Seq::<i64>::new(1, |_j: int| elem_at_i_minus_1).add(seq.skip(i)));
        
        // Use recursion on i - 1
        count_frequency_spec_properties(seq, key, i - 1);
        
        // Now prove the relationship
        let count_take_i_minus_1 = count_frequency_spec(seq.take(i - 1), key);
        let count_skip_i_minus_1 = count_frequency_spec(seq.skip(i - 1), key);
        let count_skip_i = count_frequency_spec(seq.skip(i), key);
        let count_take_i = count_frequency_spec(seq.take(i), key);
        
        // seq.take(i) = seq.take(i-1).push(elem_at_i_minus_1)
        assert(seq.take(i) =~= seq.take(i - 1).push(elem_at_i_minus_1));
        
        if elem_at_i_minus_1 == key {
            assert(count_take_i == count_take_i_minus_1 + 1);
            assert(count_skip_i_minus_1 == count_skip_i + 1);
        } else {
            assert(count_take_i == count_take_i_minus_1);
            assert(count_skip_i_minus_1 == count_skip_i);
        }
    }
}

// Helper to show filtering preserves the count relationship
proof fn filter_preserves_single_occurrence(numbers: Seq<i64>, result: Seq<i64>, i: int)
    requires 
        0 <= i <= numbers.len(),
        result == numbers.take(i).filter(|x: i64| count_frequency_spec(numbers, x) == 1),
    ensures
        forall|j: int| #![auto] 0 <= j < result.len() ==> count_frequency_spec(numbers, result[j]) == 1,
{
    assert forall|j: int| 0 <= j < result.len() implies count_frequency_spec(numbers, result[j]) == 1 by {
        let elem = result[j];
        assert(numbers.take(i).filter(|x: i64| count_frequency_spec(numbers, x) == 1).contains(elem));
    }
}

// Helper to relate count_frequency_spec on take with full sequence
proof fn count_frequency_take_full(seq: Seq<i64>, key: i64, n: int)
    requires 0 <= n <= seq.len(),
    ensures 
        count_frequency_spec(seq.take(n), key) <= count_frequency_spec(seq, key),
        count_frequency_spec(seq.skip(n), key) >= 0,
    decreases seq.len() - n,
{
    if n == seq.len() {
        assert(seq.take(n) =~= seq);
        assert(seq.skip(n) =~= Seq::<i64>::empty());
    } else {
        count_frequency_spec_properties(seq, key, n);
    }
}

// Helper to ensure count fits in u64
proof fn count_in_bounds(seq: Seq<i64>, key: i64)
    requires seq.len() <= u64::MAX,
    ensures 0 <= count_frequency_spec(seq, key) <= seq.len() <= u64::MAX,
    decreases seq.len(),
{
    if seq.len() == 0 {
        assert(count_frequency_spec(seq, key) == 0);
    } else {
        count_in_bounds(seq.drop_last(), key);
        assert(count_frequency_spec(seq.drop_last(), key) <= seq.drop_last().len());
        if seq.last() == key {
            assert(count_frequency_spec(seq, key) == count_frequency_spec(seq.drop_last(), key) + 1);
        } else {
            assert(count_frequency_spec(seq, key) == count_frequency_spec(seq.drop_last(), key));
        }
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
            0 <= i <= numbers_len,
            unique_numbers@ == numbers@.take(i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let current = numbers[i];
        let mut count = 0u64;
        
        // Count occurrences of current element
        for j in 0..numbers_len
            invariant
                0 <= i < numbers_len,
                0 <= j <= numbers_len,
                count <= j,
                count == count_frequency_spec(numbers@.take(j as int), current) as u64,
        {
            if numbers[j] == current {
                proof {
                    count_in_bounds(numbers@.take((j + 1) as int), current);
                    assert(j + 1 <= numbers_len);
                    assert(numbers@.take((j + 1) as int).len() == j + 1);
                    assert(count_frequency_spec(numbers@.take((j + 1) as int), current) <= j + 1);
                }
                count = count + 1;
                
                proof {
                    assert(j < numbers@.len());
                    assert(numbers@.take((j + 1) as int) =~= numbers@.take(j as int).push(numbers@[j as int]));
                    assert(numbers@[j as int] == current);
                    assert(count_frequency_spec(numbers@.take((j + 1) as int), current) == 
                           count_frequency_spec(numbers@.take(j as int), current) + 1);
                }
            } else {
                proof {
                    assert(j < numbers@.len());
                    assert(numbers@.take((j + 1) as int) =~= numbers@.take(j as int).push(numbers@[j as int]));
                    assert(numbers@[j as int] != current);
                    assert(count_frequency_spec(numbers@.take((j + 1) as int), current) == 
                           count_frequency_spec(numbers@.take(j as int), current));
                }
            }
        }
        
        // Add to result if count is exactly 1
        proof {
            assert(numbers_len as int == numbers@.len());
            assert(numbers@.take(numbers@.len()) =~= numbers@);
            count_in_bounds(numbers@, current);
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
        assert(numbers@.take(numbers@.len()) =~= numbers@);
    }
    
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}