// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)

    requires
        list.len() > 0,
        0 < k < list@.len(),

    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added conditions from the requires clause to the loop invariants to provide more context to the verifier */
    let mut new_list = Vec::new();
    let mut i: usize = 0;
    while i < k - 1
        invariant
            0 < k,
            (k as nat) < list@.len(),
            i <= k - 1,
            new_list@ == list@.subrange(0, i as int),
        decreases k - 1 - i
    {
        new_list.push(list[i]);
        i = i + 1;
    }

    let mut j: usize = k;
    while j < list.len()
        invariant
            0 < k,
            (k as nat) < list@.len(),
            new_list@ == list@.subrange(0, k - 1 as int).add(list@.subrange(k as int, j as int)),
            k <= j <= list.len(),
        decreases list.len() - j
    {
        new_list.push(list[j]);
        j = j + 1;
    }

    new_list
}
// </vc-code>

}
fn main() {}