// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

spec fn is_first_even(even_index: int, lst: Seq<i32>) -> bool
    recommends 0 <= even_index < lst.len(), is_even(lst[even_index] as int)
{
    forall|i: int| 0 <= i < even_index ==> is_odd(lst[i] as int)
}

spec fn is_first_odd(odd_index: int, lst: Seq<i32>) -> bool
    recommends 0 <= odd_index < lst.len(), is_odd(lst[odd_index] as int)
{
    forall|i: int| 0 <= i < odd_index ==> is_even(lst[i] as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Replaced `unreachable!()` with Verus's `unreached()` to fix compilation error. */
fn find_first_even_index(lst: &Vec<i32>) -> (result: usize)
    requires
        exists|i: int| 0 <= i < lst@.len() && is_even(lst@[i] as int),
    ensures
        0 <= result < lst@.len(),
        is_even(lst@[result as int] as int),
        is_first_even(result as int, lst@),
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> is_odd(lst@[j] as int),
        decreases lst.len() - i
    {
        if lst[i] % 2 == 0 {
            return i;
        }
        i = i + 1;
    }
    unreached()
}

/* helper modified by LLM (iteration 3): Replaced `unreachable!()` with Verus's `unreached()` to fix compilation error. */
fn find_first_odd_index(lst: &Vec<i32>) -> (result: usize)
    requires
        exists|i: int| 0 <= i < lst@.len() && is_odd(lst@[i] as int),
    ensures
        0 <= result < lst@.len(),
        is_odd(lst@[result as int] as int),
        is_first_odd(result as int, lst@),
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> is_even(lst@[j] as int),
        decreases lst.len() - i
    {
        if lst[i] % 2 != 0 {
            return i;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_indices(lst: Vec<i32>) -> (result: (usize, usize))
    requires lst.len() >= 2,
             exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
             exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int)
    ensures 0 <= result.0 < lst.len(),
            0 <= result.1 < lst.len(),

            is_even(lst[result.0 as int] as int) && is_first_even(result.0 as int, lst@),
            is_odd(lst[result.1 as int] as int) && is_first_odd(result.1 as int, lst@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Calling the fixed helper functions. */
    let even_idx = find_first_even_index(&lst);
    let odd_idx = find_first_odd_index(&lst);
    (even_idx, odd_idx)
}
// </vc-code>

}
fn main() {}