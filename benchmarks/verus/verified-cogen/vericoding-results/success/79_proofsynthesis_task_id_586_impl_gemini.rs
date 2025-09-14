// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)

    requires
        list@.len() > 0,
        0 < n < list@.len(),

    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): add decreases clauses to loops */
    let mut new_list = Vec::new();
    let len = list.len();

    let mut i: usize = n;
    while i < len
        invariant
            len == list@.len(),
            0 < n < len,
            n <= i <= len,
            new_list@ == list@.subrange(n as int, i as int),
        decreases len - i
    {
        new_list.push(list[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n
        invariant
            len == list@.len(),
            0 < n < len,
            0 <= j <= n,
            new_list@ == list@.subrange(n as int, len as int).add(list@.subrange(0, j as int)),
        decreases n - j
    {
        new_list.push(list[j]);
        j = j + 1;
    }

    new_list
}
// </vc-code>

}
fn main() {}