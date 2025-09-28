// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_up_to(numbers: Seq<int>, index: int) -> int
    decreases index when 0 <= index < numbers.len()
{
    if 0 <= index < numbers.len() {
        if index == 0 {
            numbers[0]
        } else {
            let prev_max = max_up_to(numbers, index - 1);
            if numbers[index] > prev_max { numbers[index] } else { prev_max }
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_to_seq_int(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 5): added comprehensive lemmas for proving postconditions */
proof fn max_up_to_lemma(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        forall|j: int| 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i),
        exists|k: int| 0 <= k <= i && numbers[k] == max_up_to(numbers, i),
    decreases i
{
    if i == 0 {
        assert(numbers[0] == max_up_to(numbers, 0));
    } else {
        max_up_to_lemma(numbers, i - 1);
        let prev_max = max_up_to(numbers, i - 1);
        if numbers[i] > prev_max {
            assert(max_up_to(numbers, i) == numbers[i]);
        } else {
            assert(max_up_to(numbers, i) == prev_max);
        }
    }
}

proof fn rolling_max_correctness_lemma(numbers: Vec<i8>, result: Vec<i8>, idx: int)
    requires
        result.len() == numbers.len(),
        0 <= idx < result.len(),
        result[idx] as int == max_up_to(vec_to_seq_int(numbers), idx),
    ensures
        forall|j: int| 0 <= j <= idx ==> numbers@[j] as int <= result[idx] as int,
        exists|k: int| 0 <= k <= idx && numbers@[k] as int == result[idx] as int,
{
    let seq_numbers = vec_to_seq_int(numbers);
    max_up_to_lemma(seq_numbers, idx);
    assert(result[idx] as int == max_up_to(seq_numbers, idx));
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == numbers.len() &&
        (numbers.len() == 0 ==> result.len() == 0) &&
        (numbers.len() > 0 ==> result.len() > 0) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            result[i] as int == max_up_to(vec_to_seq_int(numbers), i)) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            forall|j: int| #![trigger numbers@[j]] 0 <= j <= i ==> numbers@[j] as int <= result[i] as int) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            exists|j: int| 0 <= j <= i && numbers@[j] as int == result[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors with proper int/usize conversions */
    let mut result = Vec::new();
    
    if numbers.len() == 0 {
        return result;
    }
    
    let mut i = 0;
    while i < numbers.len()
        invariant
            result.len() == i,
            i <= numbers.len(),
            forall|k: int| 0 <= k < i ==> result[k] as int == max_up_to(vec_to_seq_int(numbers), k),
            forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j <= k ==> numbers@[j] as int <= result[k] as int,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j <= k && numbers@[j] as int == result[k] as int,
        decreases numbers.len() - i
    {
        let current_max = if i == 0 {
            numbers[0]
        } else {
            let prev_max = result[i - 1];
            if numbers[i as int] > prev_max { numbers[i as int] } else { prev_max }
        };
        
        result.push(current_max);
        
        proof {
            let seq_numbers = vec_to_seq_int(numbers);
            max_up_to_lemma(seq_numbers, i as int);
            
            assert(result[i as int] as int == current_max as int);
            
            if i == 0 {
                assert(current_max == numbers[0]);
                assert(max_up_to(seq_numbers, 0) == seq_numbers[0]);
                assert(seq_numbers[0] == numbers@[0] as int);
                assert(result[i as int] as int == max_up_to(seq_numbers, i as int));
            } else {
                let prev_max = result[i - 1];
                if numbers[i as int] > prev_max {
                    assert(current_max == numbers[i as int]);
                    assert(numbers[i as int] as int == max_up_to(seq_numbers, i as int));
                } else {
                    assert(current_max == prev_max);
                    assert(prev_max as int == max_up_to(seq_numbers, (i - 1) as int));
                    assert(max_up_to(seq_numbers, i as int) == max_up_to(seq_numbers, (i - 1) as int));
                }
                assert(result[i as int] as int == max_up_to(seq_numbers, i as int));
            }
            
            rolling_max_correctness_lemma(numbers, result, i as int);
        }
        
        i += 1;
    }
    
    proof {
        let seq_numbers = vec_to_seq_int(numbers);
        assert(forall|k: int| 0 <= k < result.len() ==> {
            rolling_max_correctness_lemma(numbers, result, k);
            true
        });
    }
    
    result
}
// </vc-code>


}

fn main() {}