// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained dummy helper to satisfy placeholder */
fn helpers_dummy() { }

// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): insertion sort using usize indices with nat casts for specs */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0usize;
    while i < l.len()
        invariant
            i as nat <= l@.len(),
            forall|a: nat, b: nat| a < b && b < res@.len() ==> res@.index(a) <= res@.index(b),
            res@.to_multiset() == l@.slice(0, i as nat).to_multiset(),
        decreases l.len() - i
    {
        let x: i32 = l@.index(i as nat);

        let mut k: usize = 0usize;
        while k < res.len()
            invariant
                k as nat <= res@.len(),
                forall|a: nat, b: nat| a < b && b < res@.len() ==> res@.index(a) <= res@.index(b),
            decreases res.len() - k
        {
            if res@.index(k as nat) <= x {
                k = k + 1;
            } else {
                break;
            }
        }

        res.insert(k, x);

        i = i + 1;
    }

    res
}

// </vc-code>

}
fn main() {}