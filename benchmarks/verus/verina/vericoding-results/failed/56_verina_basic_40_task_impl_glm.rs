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

// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): made min_val mutable */
{
    let mut min_val = s[0];
    for i in 1..s.len()
        invariant
            forall|j: int| 0 <= j < i ==> min_val <= s[j],
            exists|j: int| 0 <= j < i && s[j] == min_val,
        decreases s.len() - i
    {
        if s[i] < min_val {
            min_val = s[i];
        }
    }

    let mut second_min = None;
    for i in 0..s.len()
        invariant
            second_min.is_none() ==> forall|j: int| 0<=j<i ==> s[j] == min_val,
            second_min.is_some() ==> {
                let x = second_min.unwrap();
                min_val < x &&
                (forall|j: int| 0<=j<i ==> s[j] == min_val || s[j] >= x) &&
                (exists|j: int| 0<=j<i && s[j] == x)
            },
        decreases s.len() - i
    {
        if s[i] > min_val {
            if second_min.is_none() || s[i] < second_min.unwrap() {
                second_min = Some(s[i]);
            }
        }
    }

    if second_min.is_none() {
        assert(false);
    }

    second_min.unwrap()
}
// </vc-code>

}
fn main() {}