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
/* helper modified by LLM (iteration 5): find index of minimal element */
fn min_index(s: &Vec<i32>) -> (res: usize)
    requires
        s.len() > 0,
    ensures
        res < s.len(),
        forall|k: usize| k < s.len() ==> s[res as int] <= s[k as int],
{
    let n = s.len();
    let mut i: usize = 1;
    let mut idx: usize = 0;
    while i < n
        invariant
            i <= n,
            idx < s.len(),
            forall|k: usize| k < i ==> s[idx as int] <= s[k as int],
        decreases n - i
    {
        if s[i] < s[idx] {
            idx = i;
        }
        i = i + 1;
    }
    idx
}

/* helper modified by LLM (iteration 5): find index of minimal element excluding given value */
fn min_index_excluding(s: &Vec<i32>, excl: i32) -> (res: usize)
    requires
        exists|i: usize| i < s.len() && s[i as int] != excl,
    ensures
        res < s.len(),
        s[res as int] != excl,
        forall|k: usize| k < s.len() && s[k as int] != excl ==> s[res as int] <= s[k as int],
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n && s[i] == excl
        invariant
            i <= n,
            forall|k: usize| k < i ==> s[k as int] == excl,
        decreases n - i
    {
        i = i + 1;
    }
    let mut idx: usize = i;
    i = i + 1;
    while i < n
        invariant
            i <= n,
            idx < s.len(),
            s[idx as int] != excl,
            forall|k: usize| k < i && s[k as int] != excl ==> s[idx as int] <= s[k as int],
        decreases n - i
    {
        if s[i] != excl && s[i] < s[idx] {
            idx = i;
        }
        i = i + 1;
    }
    idx
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute second smallest using helpers with usize indices */
    let min_i = min_index(s);
    let excl = s[min_i];
    let sec_i = min_index_excluding(s, excl);
    s[sec_i]
}
// </vc-code>

}
fn main() {}