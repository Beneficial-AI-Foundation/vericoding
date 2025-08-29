use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    assert(vec.push(i).len() == vec.len() + 1);
    assert(vec.push(i).last() == i);
    assert(vec.push(i).index(l as int) == vec.push(i).index(vec.len() as int));
    assert(vec.push(i).index(vec.len() as int) == i);
}

proof fn lemma_contains_preservation<T>(original: Seq<T>, filtered: Seq<T>, elem: T)
    requires
        forall |k: int| 0 <= k < filtered.len() ==> original.contains(filtered[k]),
        original.contains(elem),
    ensures
        filtered.push(elem).len() == filtered.len() + 1,
        forall |k: int| 0 <= k < filtered.len() ==> filtered.push(elem)[k] == filtered[k],
        forall |k: int| 0 <= k < filtered.push(elem).len() ==> original.contains(filtered.push(elem)[k]),
{
    let new_seq = filtered.push(elem);
    assert(new_seq.len() == filtered.len() + 1);
    assert(new_seq[filtered.len() as int] == elem);
    
    assert(forall |k: int| 0 <= k < filtered.len() ==> new_seq[k] == filtered[k]);
    assert(forall |k: int| 0 <= k < new_seq.len() ==> {
        if k < filtered.len() {
            original.contains(new_seq[k])
        } else {
            k == filtered.len() && new_seq[k] == elem && original.contains(elem)
        }
    });
}

proof fn lemma_push_maintains_invariant(old_result: Seq<i32>, elem: i32, v_seq: Seq<i32>, i: int)
    requires
        v_seq.contains(elem),
        elem <= (spec_fn_with_requires_and_ensures! { |e: i32| true } ensures |result: i32| result == elem) (elem),
        forall |k: int| 0 <= k < i && v_seq[k] <= elem ==> old_result.contains(v_seq[k]),
    ensures
        forall |k: int| 0 <= k <= i && v_seq[k] <= elem ==> old_result.push(elem).contains(v_seq[k]),
{
    let new_seq = old_result.push(elem);
    assert(forall |k: int| 0 <= k < i && v_seq[k] <= elem ==> {
        old_result.contains(v_seq[k]) && new_seq.contains(v_seq[k])
    });
    assert(new_seq.contains(elem));
    assert(v_seq[i] == elem);
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
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): fixed proof block syntax and old() usage */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            proof {
                lemma_contains_preservation(v@, result@, v[i as int]);
                let old_result_seq = result@;
                assert(v@.contains(v[i as int]));
                assert(forall |k: int| 0 <= k < i && v[k] <= e ==> old_result_seq.contains(v[k]));
            }
            result.push(v[i]);
            proof {
                let old_result_seq = result@.drop_last();
                assert(forall |k: int| 0 <= k < i && v[k] <= e ==> {
                    old_result_seq.contains(v[k]) && result@.contains(v[k])
                });
                assert(result@.contains(v[i as int]));
                assert(forall |k: int| 0 <= k <= i && v[k] <= e ==> result@.contains(v[k]));
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}

fn main() {}