use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_seq_max_monotonic(a: Seq<i32>, x: i32)
    requires a.len() > 0
    ensures seq_max(a.push(x)) == if x > seq_max(a) { x } else { seq_max(a) }
    decreases a.len()
{
    if a.len() == 1 {
        assert(a.push(x).drop_last() == a);
        assert(a.push(x).last() == x);
    } else {
        lemma_seq_max_monotonic(a.drop_last(), x);
        assert(a.push(x).drop_last() == a);
        assert(a.push(x).last() == x);
    }
}

proof fn lemma_seq_max_take_extend(numbers: Seq<i32>, i: int)
    requires 0 < i < numbers.len()
    ensures seq_max(numbers.take(i + 1)) == if numbers[i] > seq_max(numbers.take(i)) { numbers[i] } else { seq_max(numbers.take(i)) }
{
    let prefix = numbers.take(i);
    let extended = numbers.take(i + 1);
    assert(extended == prefix.push(numbers[i]));
    lemma_seq_max_monotonic(prefix, numbers[i]);
}

proof fn lemma_seq_max_single(a: Seq<i32>, i: int)
    requires a.len() > 0, 0 <= i < a.len()
    ensures seq_max(a.take(1)) == a[0]
{
    let single = a.take(1);
    assert(single.len() == 1);
    assert(single[0] == a[0]);
    assert(single.last() == a[0]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def rolling_max(numbers: List[int]) -> Tuple[int, int]"
docstring: |
From a given list of integers, generate a list of rolling maximum element found until given moment
in the sequence.
test_cases:
- input: [1, 2, 3, 2, 3, 4, 2]
expected_output: [1, 2, 3, 3, 3, 4, 4]
*/
// </vc-description>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    if numbers.len() == 0 {
        return result;
    }
    
    let mut i = 0;
    let mut current_max = numbers[0];
    
    /* code modified by LLM (iteration 5): establish initial invariant with proof */
    proof {
        lemma_seq_max_single(numbers@, 0);
    }
    
    result.push(current_max);
    
    /* code modified by LLM (iteration 5): added decreases clause for loop termination */
    while i + 1 < numbers.len()
        invariant
            0 <= i < numbers.len(),
            result.len() == i + 1,
            current_max == seq_max(numbers@.take(i + 1)),
            forall|j: int| 0 <= j <= i ==> result@[j] == seq_max(numbers@.take(j + 1)),
        decreases numbers.len() - i
    {
        i = i + 1;
        
        proof {
            lemma_seq_max_take_extend(numbers@, i as int);
        }
        
        if numbers[i] > current_max {
            current_max = numbers[i];
        }
        
        result.push(current_max);
    }
    
    result
}
// </vc-code>

}
fn main() {}