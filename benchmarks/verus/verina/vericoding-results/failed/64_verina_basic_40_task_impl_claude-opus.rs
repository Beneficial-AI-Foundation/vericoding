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
/* helper modified by LLM (iteration 5): Fixed lemma logic for equal values case */
spec fn is_min(s: &Vec<i32>, val: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == val) &&
    (forall|j: int| 0 <= j < s.len() ==> s[j] >= val)
}

spec fn is_second_min(s: &Vec<i32>, val: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == val) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < val &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= val))
}

proof fn lemma_second_min_postcond(s: &Vec<i32>, min1: i32, min2: i32)
    requires
        s.len() > 1,
        min1 <= min2,
        exists|j: int| 0 <= j < s.len() && s[j] == min1,
        exists|k: int| 0 <= k < s.len() && s[k] == min2,
        forall|m: int| 0 <= m < s.len() ==> s[m] >= min1,
        forall|n: int| 0 <= n < s.len() && s[n] != min1 ==> s[n] >= min2,
    ensures
        second_smallest_postcond(s, min2),
{
    assert(exists|i: int| 0 <= i < s.len() && s[i] == min2);
    assert(exists|j: int| 0 <= j < s.len() && s[j] < min2) by {
        let witness_j = choose|j: int| 0 <= j < s.len() && s[j] == min1;
        assert(s[witness_j] == min1);
        assert(min1 <= min2);
        assert(s[witness_j] <= min2);
        assert(s[witness_j] < min2);
    };
    assert(forall|k: int| 0 <= k < s.len() && s[k] != min1 ==> s[k] >= min2);
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed initial values handling and loop invariants */
    let mut min1: i32;
    let mut min2: i32;
    
    if s[0] <= s[1] {
        min1 = s[0];
        min2 = s[1];
    } else {
        min1 = s[1];
        min2 = s[0];
    }
    
    let mut i = 2;
    while i < s.len()
        invariant
            2 <= i <= s.len(),
            min1 <= min2,
            exists|j: int| 0 <= j < i && s[j] == min1,
            exists|k: int| 0 <= k < i && s[k] == min2,
            forall|m: int| 0 <= m < i ==> s[m] >= min1,
            forall|n: int| 0 <= n < i && s[n] != min1 ==> s[n] >= min2,
        decreases s.len() - i
    {
        if s[i] < min1 {
            min2 = min1;
            min1 = s[i];
        } else if s[i] < min2 && s[i] != min1 {
            min2 = s[i];
        }
        i = i + 1;
    }
    
    assert(min1 < min2) by {
        assert(forall|m: int| 0 <= m < s.len() ==> s[m] >= min1);
        assert(forall|n: int| 0 <= n < s.len() && s[n] != min1 ==> s[n] >= min2);
        assert(exists|k: int| 0 <= k < s.len() && s[k] == min2);
        assert(min1 <= min2);
        if min1 == min2 {
            assert(forall|m: int| 0 <= m < s.len() ==> s[m] >= min1);
            assert(forall|m: int| 0 <= m < s.len() ==> s[m] == min1);
            assert(s.len() > 1);
            assert(s[0] == min1);
            assert(s[1] == min1);
            assert(false);
        }
    };
    
    proof {
        lemma_second_min_postcond(s, min1, min2);
    }
    
    min2
}
// </vc-code>

}
fn main() {}