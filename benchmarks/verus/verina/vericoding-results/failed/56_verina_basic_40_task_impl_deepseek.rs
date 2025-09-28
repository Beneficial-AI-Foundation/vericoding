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
/* helper modified by LLM (iteration 5): Fixed function signature syntax and return types */
proof fn lemma_exists_min(s: Seq<int>, start: int, end: int) -> (min_val: int, min_index: int)
    requires 0 <= start <= end <= s.len()
    ensures 
        start <= min_index < end,
        s[min_index] == min_val,
        forall|k: int| start <= k < end ==> s[k] >= min_val
{
    if start == end {
        (0, start)
    } else {
        let (sub_min, sub_index) = lemma_exists_min(s, start + 1, end);
        if s[start] <= sub_min {
            (s[start], start)
        } else {
            (sub_min, sub_index)
        }
    }
}

proof fn lemma_second_smallest_exists(s: Seq<int>) -> (min_val: int, second_min: int)
    requires s.len() > 1
    ensures 
        exists|i: int| 0 <= i < s.len() && s[i] == second_min,
        exists|j: int| 0 <= j < s.len() && s[j] < second_min,
        forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= second_min
{
    let (min_val, min_index) = lemma_exists_min(s, 0, s.len());
    let filtered_s = s.filter(|&x| x != min_val);
    assert(filtered_s.len() > 0);
    let (second_min, second_index) = lemma_exists_min(filtered_s, 0, filtered_s.len());
    (min_val, second_min)
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error and implemented proper logic */
    let mut min1 = s[0];
    let mut min2 = s[1];
    
    if min2 < min1 {
        let temp = min1;
        min1 = min2;
        min2 = temp;
    }
    
    let mut i = 2;
    while i < s.len()
        invariant
            2 <= i <= s.len(),
            min1 <= min2,
            exists|j: int| 0 <= j < i && s[j] == min1,
            exists|k: int| 0 <= k < i && s[k] == min2,
            forall|m: int| 0 <= m < i ==> s[m] >= min1
        decreases s.len() - i
    {
        let current = s[i];
        if current < min1 {
            min2 = min1;
            min1 = current;
        } else if current < min2 {
            min2 = current;
        }
        i += 1;
    }
    
    min2
}
// </vc-code>

}
fn main() {}