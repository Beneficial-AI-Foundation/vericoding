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

/* helper modified by LLM (iteration 5): [no changes needed for helper functions] */
proof fn lemma_max_up_to_is_upper_bound(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        forall|j: int| 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i),
    decreases i
{
    if i > 0 {
        lemma_max_up_to_is_upper_bound(numbers, i - 1);
    }
}

/* helper modified by LLM (iteration 5): [no changes needed for helper functions] */
proof fn lemma_max_up_to_is_in_seq(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        exists|j: int| 0 <= j <= i && numbers[j] == max_up_to(numbers, i),
    decreases i
{
    if i > 0 {
        lemma_max_up_to_is_in_seq(numbers, i - 1);
        let prev_max = max_up_to(numbers, i - 1);
        let current_max = max_up_to(numbers, i);
        if numbers[i] > prev_max {
            assert(current_max == numbers[i]);
        } else {
            assert(current_max == prev_max);
            let k = choose |k: int| 0 <= k <= i - 1 && numbers[k] == prev_max;
            assert(0 <= k <= i);
            assert(numbers[k] == current_max);
        }
    } else {
        assert(max_up_to(numbers, 0) == numbers[0]);
    }
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
/* code modified by LLM (iteration 5): [added triggers to fix verification error and simplified proofs] */
{
    let mut result = Vec::new();
    if numbers.len() == 0 {
        return result;
    }

    result.push(numbers[0]);

    let mut i: usize = 1;
    while i < numbers.len()
        invariant
            numbers.len() > 0,
            1 <= i <= numbers.len(),
            result.len() == i,
            forall|j: int| #![trigger result@[j]] 0 <= j < i ==> result@[j] as int == max_up_to(vec_to_seq_int(numbers), j),
        decreases numbers.len() - i
    {
        let prev_max = result[(i-1) as usize];
        let current_val = numbers[i as usize];
        if current_val > prev_max {
            result.push(current_val);
        } else {
            result.push(prev_max);
        }
        proof {
            let s = vec_to_seq_int(numbers);
            let k = (i - 1) as int;
            assert(prev_max as int == max_up_to(s, k));
            assert(max_up_to(s, i as int) == if s[i as int] > max_up_to(s, k) { s[i as int] } else { max_up_to(s, k) });
        }
        i = i + 1;
    }

    proof {
        let s = vec_to_seq_int(numbers);
        assert forall|i: int| #![trigger result@[i]] 0 <= i < result.len() implies
            result@[i] as int == max_up_to(s, i) by {}

        assert forall|i: int| #![trigger result@[i]] 0 <= i < result.len() implies
            forall|j: int| #![trigger numbers@[j]] 0 <= j <= i ==> numbers@[j] as int <= result@[i] as int
        by {
            lemma_max_up_to_is_upper_bound(s, i);
        }

        assert forall|i: int| #![trigger result@[i]] 0 <= i < result.len() implies
            exists|j: int| 0 <= j <= i && numbers@[j] as int == result@[i] as int
        by {
            lemma_max_up_to_is_in_seq(s, i);
        }
    }

    result
}
// </vc-code>


}

fn main() {}