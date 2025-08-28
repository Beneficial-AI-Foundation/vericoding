use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: int)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l) == i,
{
}

proof fn lemma_vec_contains<T>(v: Vec<T>, e: T)
    requires
        v@.contains(e),
    ensures
        exists |k: int| 0 <= k < v.len() && v@[k] == e,
{
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    // pre-conditions-start
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < v.len()
        invariant
            i <= v.len(),
            forall |k: int| 0 <= k < result.len() ==> result@[k] <= e && v@.contains(result@[k]),
            forall |k: int| 0 <= k < i && v@[k] <= e ==> result@.contains(v@[k]),
    {
        if v[i] <= e {
            result.push(v[i]);
            proof {
                assert(v@.contains(v[i]));
                lemma_vec_push(result@, v[i], result.len() as int - 1);
            }
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}

fn main() {}