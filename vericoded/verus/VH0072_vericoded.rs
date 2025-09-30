// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn strange_sort_list_helper(s: Vec<i8>) -> (res: (Vec<i8>, Vec<i8>))
    ensures 
        s@.to_multiset() == res.0@.to_multiset(),
        s@.len() == res.0@.len() && s@.len() == res.1@.len(),
        forall|i: int| 0 <= i < s@.len() && i % 2 == 0 ==> res.1@[i] == res.0@[i / 2],
        forall|i: int| 0 <= i < s@.len() && i % 2 == 1 ==> res.1@[i] == res.0@[s@.len() - (i - 1) / 2 - 1]
// </vc-spec>
// <vc-code>
{
    let res0 = s;
    let n = res0.len();
    let mut res1: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res0@.len() == n as int,
            0 <= i as int <= n as int,
            res1@.len() == i as int,
            forall|j: int| 0 <= j < i as int && j % 2 == 0 ==> res1@[j] == res0@[j / 2],
            forall|j: int| 0 <= j < i as int && j % 2 == 1 ==> res1@[j] == res0@[n as int - (j - 1) / 2 - 1],
        decreases n as int - i as int
    {
        if i % 2 == 0 {
            let k = i / 2;
            assert(k <= i);
            assert(i < n);
            assert(k < n);
            let v = res0[k];
            res1.push(v);
        } else {
            assert(i >= 1);
            assert(i < n);
            let q = (i - 1) / 2;
            assert(q <= i / 2);
            assert(i / 2 <= i);
            assert(q < n);
            assert(q + 1 <= n);
            let k = n - q - 1;
            assert(k < n);
            let v = res0[k];
            res1.push(v);
        }
        i += 1;
    }
    (res0, res1)
}
// </vc-code>


}

fn main() {}