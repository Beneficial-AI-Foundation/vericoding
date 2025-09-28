use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn lemma_max_properties(a: int, b: int, m: int)
    requires m == max(a, b),
    ensures 
        m >= a && m >= b,
        m == a || m == b
{
}

proof fn lemma_isMax_implies_some_value(m: int, numbers: Seq<int>)
    requires 
        numbers.len() > 0,
        isMax(m, numbers),
    ensures 
        numbers.contains(m)
{
}

proof fn lemma_isMax_max_value(a: int, b: int, numbers: Seq<int>)
    requires 
        numbers.len() > 0,
        isMax(max(a, b), numbers),
    ensures 
        numbers.contains(max(a, b))
{
}

proof fn lemma_subrange_contains_first_element<T>(s: Seq<T>, i: int)
    requires 
        0 <= i < s.len(),
    ensures 
        s.subrange(0, i + 1).contains(s[i])
{
}

proof fn lemma_max_is_max_in_subrange(m: int, numbers: Seq<int>, i: int)
    requires 
        0 <= i < numbers.len(),
        isMax(m, numbers.subrange(0, i + 1)),
    ensures 
        forall|j: int| 0 <= j <= i ==> numbers[j] <= m
{
}

proof fn lemma_extend_max(new_val: int, current_max: int, numbers: Seq<int>, i: int)
    requires 
        0 <= i < numbers.len(),
        isMax(current_max, numbers.subrange(0, i)),
    ensures 
        isMax(max(current_max, new_val), numbers.subrange(0, i + 1))
{
    let new_seq = numbers.subrange(0, i + 1);
    let m = max(current_max, new_val);
    
    assert(new_seq.contains(new_val)) by {
        lemma_subrange_contains_first_element(numbers, i);
    };
    assert(new_val <= m);
    assert(forall|j: int| 0 <= j < i ==> numbers[j] <= current_max);
    assert(forall|j: int| 0 <= j < i ==> numbers[j] <= m);
    assert(forall|j: int| 0 <= j <= i ==> numbers[j] <= m);
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut current_max = numbers[0];
    result.push(current_max);
    
    let mut n: usize = 1;
    while n < numbers.len()
        invariant
            n >= 1,
            n <= numbers.len(),
            result.len() == n,
            forall|i: int| 0 < i < n ==> isMax(result@[i], numbers@.subrange(0, i + 1)),
            isMax(current_max, numbers@.subrange(0, n as int)),
        decreases numbers.len() - n
    {
        let old_current_max = current_max;
        current_max = if numbers[n] > current_max { numbers[n] } else { current_max };
        proof {
            lemma_extend_max(numbers[n], old_current_max, numbers@, n as int);
        }
        result.push(current_max);
        n = n + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}