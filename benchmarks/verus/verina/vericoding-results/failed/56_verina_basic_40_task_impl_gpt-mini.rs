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
/* helper modified by LLM (iteration 5): index casting helper */
proof fn index_casting_helper() { }

// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int indices for spec and usize casts for runtime indexing */
    let n: int = s.len() as int;
    let mut i: int = 2;
    let mut min_i: int;
    let mut second_i: int;

    if s[0 as usize] <= s[1 as usize] {
        min_i = 0;
        second_i = 1;
    } else {
        min_i = 1;
        second_i = 0;
    }

    while i < n
        invariant
            0 <= i,
            i <= n,
            0 <= min_i,
            0 <= second_i,
            min_i < i,
            second_i < i,
            forall|k: int| 0 <= k && k < i ==> s[k] >= s[min_i],
            forall|k: int| 0 <= k && k < i && s[k] != s[min_i] ==> s[k] >= s[second_i],
        decreases n - i
    {
        let x: i32 = s[i as usize];
        if x < s[min_i as usize] {
            second_i = min_i;
            min_i = i;
        } else {
            if x != s[min_i as usize] && x < s[second_i as usize] {
                second_i = i;
            }
        }
        i = i + 1;
    }

    s[second_i as usize]
}
// </vc-code>

}
fn main() {}