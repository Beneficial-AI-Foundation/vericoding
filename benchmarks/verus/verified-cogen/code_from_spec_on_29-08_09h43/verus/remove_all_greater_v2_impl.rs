use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_vec_push<T>(vec: Seq<T>, elem: T, l: int)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(elem)[k],
        vec.push(elem).index(l) == elem,
{
    assert(vec.push(elem).len() == vec.len() + 1);
    assert(vec.push(elem).index(l) == elem);
    assert(forall |k: int| 0 <= k < vec.len() ==> vec[k] == vec.push(elem)[k]);
}

proof fn lemma_contains_push<T>(s: Seq<T>, x: T, y: T)
    ensures
        s.push(x).contains(y) == (s.contains(y) || x == y),
{
    /* code modified by LLM (iteration 4): added proof body for contains push lemma */
    if s.push(x).contains(y) {
        if s.contains(y) {
        } else {
            let idx = s.push(x).index_of(y) as int;
            assert(s.push(x)[idx] == y);
            if idx < s.len() {
                assert(s[idx] == y);
                assert(s.contains(y));
            } else {
                assert(idx == s.len());
                assert(s.push(x)[idx] == x);
                assert(x == y);
            }
        }
    } else {
        assert(!s.contains(y) && x != y);
    }
}

proof fn lemma_contains_preservation<T>(s: Seq<T>, x: T)
    ensures
        s.contains(x) ==> s.push(x).contains(x),
{
    /* code modified by LLM (iteration 4): added proof body for contains preservation */
    if s.contains(x) {
        let idx = s.index_of(x) as int;
        assert(s[idx] == x);
        assert(s.push(x)[idx] == x);
        assert(s.push(x).contains(x));
    }
}

proof fn lemma_contains_drop_last_subset<T>(s: Seq<T>, x: T)
    ensures
        s.drop_last().contains(x) ==> s.contains(x),
{
    /* code modified by LLM (iteration 4): added new helper lemma for drop_last containment */
    if s.drop_last().contains(x) {
        let idx = s.drop_last().index_of(x) as int;
        assert(s.drop_last()[idx] == x);
        assert(idx < s.drop_last().len());
        assert(s[idx] == x);
        assert(s.contains(x));
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): restructured proof to avoid calling lemma inside by block */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            result.push(v[i]);
            proof {
                lemma_vec_push(result@.drop_last(), v[i as int], result.len() as int - 1);
                lemma_contains_push(result@.drop_last(), v[i as int], v[i as int]);
                lemma_contains_preservation(result@.drop_last(), v[i as int]);
                assert(result@.contains(v[i as int]));
                
                assert(forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k])) by {
                    assert(forall |k:int| 0 <= k < i && v[k] <= e ==> result@.drop_last().contains(v[k]));
                    assert(forall |k:int| 0 <= k < i && v[k] <= e ==> {
                        let old_result = result@.drop_last();
                        old_result.contains(v[k]) && old_result.len() < result@.len() && 
                        (forall |j: int| 0 <= j < old_result.len() ==> old_result[j] == result@[j]) &&
                        result@.contains(v[k])
                    });
                }
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}

fn main() {}