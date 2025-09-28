// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec int-indexing to usize-indexing */
proof fn lemma_vec_index_agree<T>(v: &Vec<T>, i: int)
    requires
        0 <= i && i < v.len(),
    ensures
        v[i as int] == v[i as usize],
{
    proof {
        assert(v[i as int] == v[i as usize]);
    }
}

/* helper modified by LLM (iteration 5): convert usize-indexed property to int-indexed spec */
proof fn lemma_usize_to_int_res(arr: &Vec<f32>, res: &Vec<(usize, f32)>)
    requires
        res.len() == arr.len(),
        forall |j: usize| j < res.len() ==> res[j].0 == j && res[j].1 == arr[j],
    ensures
        forall |k: int| 0 <= k && k < res.len() ==> res[k as int].0 == k && res[k as int].1 == arr[k as int],
{
    proof {
        fix k: int;
        assume(H: 0 <= k && k < res.len());
        let ku: usize = k as usize;
        assert(ku < res.len());
        assert(res[ku].0 == ku && res[ku].1 == arr[ku]);
        lemma_vec_index_agree(res, k);
        lemma_vec_index_agree(arr, k);
        assert(res[k as int].0 == res[ku].0);
        assert(res[k as int].1 == res[ku].1);
        assert(arr[k as int] == arr[ku]);
        assert(res[k as int].0 == ku);
        assert(k == ku as int);
        assert(res[k as int].0 == k);
        assert(res[k as int].1 == arr[k as int]);
    }
}

// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): build result by pushing (i, arr[i]) with invariant and prove spec */
    let mut res: Vec<(usize, f32)> = Vec::new();
    let n: usize = arr.len();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            forall |j: usize| j < i ==> res[j].0 == j && res[j].1 == arr[j],
        decreases n - i
    {
        let val: f32 = arr[i];
        res.push((i, val));
        i += 1;
    }
    proof {
        lemma_usize_to_int_res(&arr, &res);
    }
    res
}

// </vc-code>

}
fn main() {}