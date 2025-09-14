// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for int index in bounds */
spec fn idx_in_bounds(list: &Vec<i32>, i: int) -> bool { 0 <= i && i < list@.len() }
// </vc-helpers>

// <vc-spec>
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)

    requires
        list@.len() > 0,
        0 < n < list@.len(),

    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices for runtime and specs for proof obligations */
    let mut res: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    let n_usize: usize = n;
    let len: usize = list.len();

    while i < n_usize
        invariant
            i <= n_usize,
            res@ == list@.subrange(n as int - i as int, n as int).reverse(),
        decreases n_usize - i
    {
        let idx_usize: usize = n_usize - 1 - i;
        proof {
            assert(idx_usize < list.len());
        }
        let x: i32 = list[idx_usize];
        res.push(x);
        i = i + 1;
    }

    let mut j: usize = n_usize;
    while j < len
        invariant
            n_usize <= j,
            j <= len,
            res@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, j as int)),
        decreases len - j
    {
        let x: i32 = list[j];
        res.push(x);
        j = j + 1;
    }

    proof {
        assert(res@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, list.len() as int)));
    }

    res
}
// </vc-code>

}
fn main() {}