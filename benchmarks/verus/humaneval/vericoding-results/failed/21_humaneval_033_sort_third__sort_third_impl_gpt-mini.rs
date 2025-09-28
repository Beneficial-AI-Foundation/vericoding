// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): selection sort that preserves multiset and returns sorted vector */
fn selection_sort_vec(v: Vec<i8>) -> (res: Vec<i8>)
    ensures
        res@.to_multiset() == v@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < res@.len() ==> res@[i] <= res@[j],
{
    let mut u = v.clone();
    let n = u.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            u@.to_multiset() == v@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i as int ==> u@[k] <= u@[l],
        decreases n - i
    {
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                i <= m && m < n,
                j <= n,
                forall|k: int| 0 <= k < j as int && k >= i as int ==> u@[m as int] <= u@[k],
            decreases n - j
        {
            if u[j] < u[m] {
                m = j;
            }
            j += 1;
        }
        if i != m {
            // swap without calling methods that take &mut self with complex args
            let tmp = u[i];
            let vm = u[m];
            u.set(i, vm);
            u.set(m, tmp);
        }
        i += 1;
    }
    u
}

// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): extract elements at indices multiple of 3, sort them, and write back */
    let mut res: Vec<i8> = a.clone();

    let n = a.len();
    let mut thirds: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            thirds@.len() <= a@.len(),
        decreases n - idx
    {
        if idx % 3 == 0 {
            thirds.push(a[idx]);
        }
        idx += 1;
    }

    let sorted_thirds = selection_sort_vec(thirds);

    let count = sorted_thirds.len();
    let mut src_i: usize = 0;
    while src_i < count
        invariant
            src_i <= count,
        decreases count - src_i
    {
        let write_pos = src_i * 3;
        res.set(write_pos, sorted_thirds[src_i]);
        src_i += 1;
    }

    res
}

// </vc-code>


}

fn main() {}