// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn second_smallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}

spec fn second_smallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == result) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < result &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>
spec fn min_two_distinct_values_exist(s: &Vec<i32>) -> bool {
    exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j]
}

spec fn count_smaller(s: &Vec<i32>, val: i32) -> int {
    s@.filter(|x: i32| x < val).len() as int
}

spec fn is_smallest(s: &Vec<i32>, val: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == val) &&
    (forall|j: int| 0 <= j < s.len() ==> s[j] >= val)
}

/* helper modified by LLM (iteration 5): added lemma to prove existence of distinct element */
proof fn lemma_distinct_element_exists(s: &Vec<i32>, smallest: i32)
    requires
        s.len() > 1,
        (forall|k: int| 0 <= k < s.len() ==> s[k] >= smallest),
        (exists|m: int| 0 <= m < s.len() && s[m] == smallest)
    ensures
        exists|idx: int| 0 <= idx < s.len() && s[idx] != smallest
{
    if forall|k: int| 0 <= k < s.len() ==> s[k] == smallest {
        assert(s[0] == smallest);
        assert(s[1] == smallest);
        assert(s[0] == s[1]);
        assert(false);
    }
}

/* helper modified by LLM (iteration 5): fixed proof to establish required preconditions */
proof fn lemma_second_smallest_properties(s: &Vec<i32>, smallest: i32, second: i32)
    requires
        s.len() > 1,
        is_smallest(s, smallest),
        (exists|i: int| 0 <= i < s.len() && s[i] == second),
        second > smallest,
        (forall|k: int| 0 <= k < s.len() && s[k] != smallest ==> s[k] >= second)
    ensures
        second_smallest_postcond(s, second)
{
    let i_idx = choose|i: int| 0 <= i < s.len() && s[i] == second;
    let j_idx = choose|j: int| 0 <= j < s.len() && s[j] == smallest;
    assert(s[i_idx] == second);
    assert(s[j_idx] == smallest);
    assert(smallest < second);
    assert(forall|k: int| 0 <= k < s.len() && s[k] != smallest ==> s[k] >= second);
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant and proof to handle case where all elements except one are equal */
    let mut smallest = s[0];
    let mut second = i32::MAX;
    let mut i = 1;
    
    // Initialize smallest from first element
    let mut j = 1;
    while j < s.len()
        invariant
            1 <= j <= s.len(),
            (forall|k: int| 0 <= k < j ==> s[k] >= smallest),
            (exists|m: int| 0 <= m < j && s[m] == smallest)
        decreases s.len() - j
    {
        if s[j] < smallest {
            smallest = s[j];
        }
        j += 1;
    }
    
    // Find second smallest
    i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            (forall|k: int| 0 <= k < s.len() ==> s[k] >= smallest),
            (exists|m: int| 0 <= m < s.len() && s[m] == smallest),
            second == i32::MAX || ((exists|n: int| 0 <= n < s.len() && s[n] == second) && second > smallest && (forall|p: int| 0 <= p < s.len() && s[p] != smallest ==> s[p] >= second))
        decreases s.len() - i
    {
        if s[i] != smallest && (second == i32::MAX || s[i] < second) {
            second = s[i];
        }
        i += 1;
    }
    
    proof {
        lemma_distinct_element_exists(s, smallest);
        assert(exists|distinct_idx: int| 0 <= distinct_idx < s.len() && s[distinct_idx] != smallest);
        assert(second != i32::MAX);
        lemma_second_smallest_properties(s, smallest, second);
    }
    
    second
}
// </vc-code>

}
fn main() {}