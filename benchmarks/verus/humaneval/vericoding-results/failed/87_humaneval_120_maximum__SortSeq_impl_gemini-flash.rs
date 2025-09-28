// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: &Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> #[trigger] sorted@[i] <= #[trigger] sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] s@[i] == #[trigger] sorted@[j],
        forall|x: i8| #[trigger] s@.contains(x) ==> #[trigger] sorted@.contains(x),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] sorted@[i] == #[trigger] s@[j],
        forall|x: i8| #[trigger] sorted@.contains(x) ==> #[trigger] s@.contains(x),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed compilation errors related to `nat`/`int` usage in ghost contexts (indices must be `usize`/`nat`, arithmetic always `int`). Cast `nat` to `int` when performing arithmetic destined for `int`-typed vars, and `int` to `nat`/`usize` when indexing. Also, adjusted loop invariants to reflect real-number arithmetic more precisely and ensure they are verifiable.] */
{
    let mut arr: Vec<i8> = s.clone();
    let n_usize: usize = arr.len();
    let n: int = n_usize as int;

    if n_usize <= 1 {
        return arr;
    }

    let mut i: nat = 1; // current element to insert
    while (i as int) < n
        invariant
            0 <= i as int <= n,
            arr@.len() as int == n,
            arr@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i as int ==> arr@[k] <= arr@[l],
        decreases n - i as int
    {
        let mut j: nat = i; // current position of the element being inserted
        while (j as int) > 0 && arr@[j as int - 1] > arr@[j as int]
            invariant
                1 <= j as int <= i as int,
                arr@.len() as int == n,
                arr@.to_multiset() == s@.to_multiset(),
                forall|k: int| 0 <= k < j as int ==> arr@[k] <= arr@[j as int],
                forall|k: int, l: int| j as int < k < l < i as int + 1 ==> arr@[k] <= arr@[l],
                forall|k: int, l: int| 0 <= k < l < j as int ==> arr@[k] <= arr@[l],
            decreases j as int
        {
            let temp = arr.index(j as usize);
            arr.set(j as usize, arr.index((j as usize).checked_sub(1).unwrap()));
            arr.set((j as usize).checked_sub(1).unwrap(), temp);

            proof {
                assert(j as int - 1 >= 0);
            }
            j = (j as int - 1) as nat;
        }
        i = (i as int + 1) as nat;
    }
    arr
}
// </vc-code>


}

fn main() {}