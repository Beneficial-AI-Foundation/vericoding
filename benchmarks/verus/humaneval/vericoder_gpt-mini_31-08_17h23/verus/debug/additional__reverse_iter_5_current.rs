use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper section updated to use nat-based indices (no extra helpers required)
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let len: nat = a.len() as nat;
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < len
        invariant { i <= len; }
        invariant { result.len() == (i as usize); }
        invariant { forall|j: nat| j < i ==> result[j as usize] == a[(len - 1 - j) as usize] }
        decreases { len - i }
    {
        result.push(a[(len - 1 - i) as usize]);
        i = i + 1;
    }

    proof {
        // show lengths match
        assert(result.len() == (len as usize));
        // show element-wise reversal for all integer indices as required by the spec
        assert(forall|k: int|
            0 <= k && k < (result.len() as int) ==>
                result[k as usize] == a[((a.len() as int) - 1 - k) as usize]
        );
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}