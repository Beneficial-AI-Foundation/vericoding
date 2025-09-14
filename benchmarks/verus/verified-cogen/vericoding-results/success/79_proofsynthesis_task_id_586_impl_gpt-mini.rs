// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): convert usize to int for specs */ spec fn usize_to_int(u: usize) -> int { u as int }
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
    /* code modified by LLM (iteration 3): implement rotation with loop invariants and proof asserts to satisfy index and subrange preconditions */
    let mut new_list = Vec::<i32>::new();
    let mut i = n;
    while i < list.len()
        invariant
            0 <= usize_to_int(n),
            usize_to_int(n) <= usize_to_int(i),
            usize_to_int(i) <= usize_to_int(list.len()),
            new_list@ == list@.subrange(usize_to_int(n), usize_to_int(i)),
        decreases
            list.len() - i
    {
        proof {
            assert(i < list.len());
        }
        new_list.push(list[i]);
        i = i + 1;
    }
    let mut j = 0usize;
    while j < n
        invariant
            0 <= usize_to_int(j),
            usize_to_int(j) <= usize_to_int(n),
            usize_to_int(n) <= usize_to_int(list.len()),
            new_list@ == list@.subrange(usize_to_int(n), usize_to_int(list.len())).add(list@.subrange(0, usize_to_int(j))),
        decreases
            n - j
    {
        proof {
            assert(j < n);
        }
        new_list.push(list[j]);
        j = j + 1;
    }
    new_list
}
// </vc-code>

}
fn main() {}