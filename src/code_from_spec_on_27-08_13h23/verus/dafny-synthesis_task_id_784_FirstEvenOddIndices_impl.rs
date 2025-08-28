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

// <vc-helpers>
proof fn lemma_first_even_exists(lst: Seq<i32>)
    requires
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
    ensures
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int) && is_first_even(i, lst),
{
    let mut i: int = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> is_odd(lst[j] as int),
    {
        if is_even(lst[i] as int) {
            return;
        }
        i = i + 1;
    }
}

proof fn lemma_first_odd_exists(lst: Seq<i32>)
    requires
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int),
    ensures
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int) && is_first_odd(i, lst),
{
    let mut i: int = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> is_even(lst[j] as int),
    {
        if is_odd(lst[i] as int) {
            return;
        }
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn first_even_odd_indices(lst: Vec<i32>) -> (result: (usize, usize))
    requires lst.len() >= 2,
             exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
             exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int)
    ensures 0 <= result.0 < lst.len(),
            0 <= result.1 < lst.len(),
            // This is the postcondition that ensures that it's the first, not just any
            is_even(lst[result.0 as int] as int) && is_first_even(result.0 as int, lst@),
            is_odd(lst[result.1 as int] as int) && is_first_odd(result.1 as int, lst@)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn first_even_odd_indices(lst: Vec<i32>) -> (result: (usize, usize))
    requires
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int),
    ensures
        0 <= result.0 < lst.len(),
        0 <= result.1 < lst.len(),
        is_even(lst[result.0 as int] as int) && is_first_even(result.0 as int, lst@),
        is_odd(lst[result.1 as int] as int) && is_first_odd(result.1 as int, lst@),
{
    let mut first_even: usize = 0;
    let mut first_odd: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;
    let mut i: usize = 0;

    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            0 <= first_even < lst.len(),
            0 <= first_odd < lst.len(),
            !found_even ==> forall|j: int| 0 <= j < i as int ==> is_odd(lst[j] as int),
            !found_odd ==> forall|j: int| 0 <= j < i as int ==> is_even(lst[j] as int),
            found_even ==> is_even(lst[first_even as int] as int) && is_first_even(first_even as int, lst@),
            found_odd ==> is_odd(lst[first_odd as int] as int) && is_first_odd(first_odd as int, lst@),
    {
        if !found_even && is_even(lst[i] as int) {
            first_even = i;
            found_even = true;
        }
        if !found_odd && is_odd(lst[i] as int) {
            first_odd = i;
            found_odd = true;
        }
        if found_even && found_odd {
            break;
        }
        i = i + 1;
    }

    proof {
        lemma_first_even_exists(lst@);
        lemma_first_odd_exists(lst@);
    }

    (first_even, first_odd)
}
// </vc-code>

fn main() {}

}