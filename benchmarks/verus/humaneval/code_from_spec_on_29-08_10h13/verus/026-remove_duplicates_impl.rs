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
spec fn count_occurrences(seq: Seq<i64>, key: i64) -> int {
    count_frequency_spec(seq, key)
}

spec fn appears_once(seq: Seq<i64>, key: i64) -> bool {
    count_occurrences(seq, key) == 1
}

spec fn remove_duplicates_spec(seq: Seq<i64>) -> Seq<i64>
    decreases seq.len()
{
    if seq.len() == 0 {
        seq![]
    } else {
        let rest = remove_duplicates_spec(seq.drop_last());
        let last_elem = seq.last();
        if appears_once(seq, last_elem) {
            rest.push(last_elem)
        } else {
            rest
        }
    }
}

proof fn count_frequency_drop_last(seq: Seq<i64>, key: i64)
    requires seq.len() > 0
    ensures count_frequency_spec(seq, key) == count_frequency_spec(seq.drop_last(), key) + if seq.last() == key { 1int } else { 0int }
{
}

proof fn count_frequency_push(seq: Seq<i64>, key: i64, elem: i64)
    ensures count_frequency_spec(seq.push(elem), key) == count_frequency_spec(seq, key) + if elem == key { 1int } else { 0int }
    decreases seq.len()
{
    if seq.len() == 0 {
        /* code modified by LLM (iteration 5): fixed base case by using definition directly */
        assert(seq.push(elem).len() == 1);
        assert(seq.push(elem).last() == elem);
        assert(seq.push(elem).drop_last().len() == 0);
        assert(count_frequency_spec(seq.push(elem).drop_last(), key) == 0);
    } else {
        /* code modified by LLM (iteration 5): added recursive case proof */
        count_frequency_push(seq.drop_last(), key, elem);
        assert(seq.push(elem).drop_last() == seq);
        assert(seq.push(elem).last() == elem);
    }
}

proof fn count_frequency_take_extend(seq: Seq<i64>, key: i64, i: int)
    requires 0 <= i < seq.len()
    ensures count_frequency_spec(seq.take(i + 1), key) == count_frequency_spec(seq.take(i), key) + if seq[i] == key { 1int } else { 0int }
{
    /* code modified by LLM (iteration 5): added lemma for extending take by one element */
    assert(seq.take(i + 1) == seq.take(i).push(seq[i]));
    count_frequency_push(seq.take(i), key, seq[i]);
}

proof fn remove_duplicates_step(seq: Seq<i64>, i: int)
    requires 0 <= i < seq.len()
    ensures remove_duplicates_spec(seq.take(i + 1)) == 
        if appears_once(seq.take(i + 1), seq[i]) {
            remove_duplicates_spec(seq.take(i)).push(seq[i])
        } else {
            remove_duplicates_spec(seq.take(i))
        }
{
    /* code modified by LLM (iteration 5): fixed postcondition to use appears_once on take(i+1) */
    let taken = seq.take(i + 1);
    assert(taken == seq.take(i).push(seq[i]));
    assert(taken.last() == seq[i]);
    assert(taken.drop_last() == seq.take(i));
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def remove_duplicates(numbers: List[int]) -> List[int]"
docstring: |
From a list of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
test_cases:
- input: [1, 2, 3, 2, 4]
expected_output: [1, 3, 4]
*/
// </vc-description>

// <vc-spec>
fn remove_duplicates(numbers: Vec<i64>) -> (result: Vec<i64>)
    ensures result@ == remove_duplicates_spec(numbers@)
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): strengthened outer loop with proper invariant maintenance */
    while i < numbers.len()
        invariant 
            i <= numbers.len(),
            result@ == remove_duplicates_spec(numbers@.take(i as int))
        decreases numbers.len() - i
    {
        let current = numbers[i];
        let mut count: i64 = 0;
        let mut j = 0;
        
        /* code modified by LLM (iteration 5): fixed inner loop with proper count tracking and overflow prevention */
        while j < numbers.len()
            invariant
                j <= numbers.len(),
                0 <= count,
                count <= j,
                count == count_frequency_spec(numbers@.take(j as int), current)
            decreases numbers.len() - j
        {
            if numbers[j] == current {
                /* code modified by LLM (iteration 5): added overflow check and proof */
                proof {
                    count_frequency_take_extend(numbers@, current, j as int);
                }
                count = count + 1;
            } else {
                /* code modified by LLM (iteration 5): added proof for non-matching case */
                proof {
                    count_frequency_take_extend(numbers@, current, j as int);
                }
            }
            j = j + 1;
        }
        
        proof {
            assert(numbers@.take(numbers.len() as int) == numbers@);
            assert(count == count_frequency_spec(numbers@, current));
        }
        
        if count == 1 {
            result.push(current);
        }
        
        i = i + 1;
        
        /* code modified by LLM (iteration 5): added complete proof for outer loop invariant */
        proof {
            let seq_i_minus_1 = numbers@.take((i - 1) as int);
            let seq_i = numbers@.take(i as int);
            assert(seq_i == seq_i_minus_1.push(current));
            assert(appears_once(numbers@.take(i as int), current) == (count == 1));
            remove_duplicates_step(numbers@, (i - 1) as int);
        }
    }
    
    proof {
        assert(numbers@.take(numbers.len() as int) == numbers@);
    }
    
    result
}
// </vc-code>

} // verus!
fn main() {}