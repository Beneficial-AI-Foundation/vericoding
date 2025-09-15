// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find first even index using recursion */
spec fn first_even_index_from(a: &Vec<i32>, idx: int) -> int
    requires 0 <= idx <= a.len(), exists|x: int| idx <= x < a.len() && is_even(a@[x])
    ensures idx <= result < a.len(), is_even(a@[result]), forall|k: int| idx <= k < result ==> is_odd(a@[k])
    decreases a.len() - idx
{
    if is_even(a@[idx]) { idx } else { first_even_index_from(a, idx + 1) }
}

/* helper modified by LLM (iteration 5): find first even index using recursion */
spec fn first_even_index(a: &Vec<i32>) -> int
    requires a.len() > 0, exists|x: int| 0 <= x < a.len() && is_even(a@[x])
    ensures 0 <= result < a.len(), is_even(a@[result]), forall|k: int| 0 <= k < result ==> is_odd(a@[k])
    decreases a.len()
{
    first_even_index_from(a, 0)
}

/* helper modified by LLM (iteration 5): find first odd index using recursion */
spec fn first_odd_index_from(a: &Vec<i32>, idx: int) -> int
    requires 0 <= idx <= a.len(), exists|x: int| idx <= x < a.len() && is_odd(a@[x])
    ensures idx <= result < a.len(), is_odd(a@[result]), forall|k: int| idx <= k < result ==> is_even(a@[k])
    decreases a.len() - idx
{
    if is_odd(a@[idx]) { idx } else { first_odd_index_from(a, idx + 1) }
}

/* helper modified by LLM (iteration 5): find first odd index using recursion */
spec fn first_odd_index(a: &Vec<i32>) -> int
    requires a.len() > 0, exists|x: int| 0 <= x < a.len() && is_odd(a@[x])
    ensures 0 <= result < a.len(), is_odd(a@[result]), forall|k: int| 0 <= k < result ==> is_even(a@[k])
    decreases a.len()
{
    first_odd_index_from(a, 0)
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost block to obtain spec indices then scan to find first even and odd and compute their difference */
    ghost {
        let _i: int = first_even_index(a);
        let _j: int = first_odd_index(a);
    }

    let mut i_usize: usize = 0;
    while i_usize < a.len() && !is_even(a[i_usize])
        invariant 0 <= i_usize <= a.len()
        decreases a.len() - i_usize
    {
        i_usize += 1;
    }

    let mut j_usize: usize = 0;
    while j_usize < a.len() && !is_odd(a[j_usize])
        invariant 0 <= j_usize <= a.len()
        decreases a.len() - j_usize
    {
        j_usize += 1;
    }

    let result: i32 = a[i_usize] - a[j_usize];
    result
}
// </vc-code>

}
fn main() {}