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
    assert forall |k: int| 0 <= k < vec.len() implies vec[k] == vec.push(i)[k] by {
        assert(vec.push(i)[k] == vec[k]);
    }
    assert(vec.push(i).index(l as int) == i);
}

spec fn contains_only_le(v: Seq<i32>, e: i32) -> bool {
    forall |k: int| 0 <= k < v.len() ==> v[k] <= e
}

spec fn all_from_original(result: Seq<i32>, original: Seq<i32>) -> bool {
    forall |k: int| 0 <= k < result.len() ==> original.contains(result[k])
}

spec fn contains_all_le(result: Seq<i32>, original: Seq<i32>, e: i32) -> bool {
    forall |k: int| 0 <= k < original.len() && original[k] <= e ==> result.contains(original[k])
}

proof fn lemma_push_preserves_contains<T>(s: Seq<T>, x: T, y: T)
    ensures s.contains(y) ==> s.push(x).contains(y)
{
    if s.contains(y) {
        assert(s.push(x).contains(y));
    }
}

proof fn lemma_push_adds_element<T>(s: Seq<T>, x: T)
    ensures s.push(x).contains(x)
{
    assert(s.push(x)[s.len() as int] == x);
    assert(s.push(x).contains(x));
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
            0 <= i <= v.len(),
            contains_only_le(result@, e),
            all_from_original(result@, v@),
            forall |k: int| 0 <= k < i && v@[k] <= e ==> result@.contains(v@[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            proof {
                let old_result = result@;
                lemma_push_adds_element(old_result, v@[i as int]);
                
                assert forall |j: int| 0 <= j < old_result.len() implies old_result.push(v@[i as int]).contains(old_result[j]) by {
                    lemma_push_preserves_contains(old_result, v@[i as int], old_result[j]);
                }
            }
            
            result.push(v[i]);
            
            proof {
                let old_result = result@.drop_last();
                
                assert forall |k: int| 0 <= k < result@.len() implies result@[k] <= e && v@.contains(result@[k]) by {
                    if k < old_result.len() {
                        assert(result@[k] == old_result[k]);
                        assert(old_result[k] <= e);
                        assert(v@.contains(old_result[k]));
                    } else {
                        assert(k == old_result.len());
                        assert(result@[k] == v@[i as int]);
                        assert(v@[i as int] <= e);
                        assert(v@.contains(v@[i as int]));
                    }
                }
                
                assert forall |k: int| 0 <= k <= i && v@[k] <= e implies result@.contains(v@[k]) by {
                    if k < i {
                        assert(old_result.contains(v@[k]));
                        lemma_push_preserves_contains(old_result, v@[i as int], v@[k]);
                        assert(result@.contains(v@[k]));
                    } else {
                        assert(k == i);
                        assert(result@[old_result.len() as int] == v@[i as int]);
                        assert(result@.contains(v@[i as int]));
                    }
                }
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}

fn main() {}