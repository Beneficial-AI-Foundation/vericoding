use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_vec_indexing<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v[i] == v@[i],
{
}

proof fn lemma_vec_len<T>(v: Vec<T>)
    ensures
        v.len() == v@.len(),
{
}

proof fn lemma_vec_eq_from_seq<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        v1@ =~= v2@,
    ensures
        v1 == v2,
{
    assert(v1@ =~= v2@);
}

proof fn lemma_vec_index_in_bounds<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
{
}

proof fn lemma_push_preserves_prev_elems<T>(v: &mut Vec<T>, val: T, j: int)
    requires
        old(v).len() == j,
        forall|k: int| 0 <= k < j ==> #[trigger] old(v)[k] == v[k],
    ensures
        v.len() == j + 1,
        forall|k: int| 0 <= k < j ==> #[trigger] v[k] == old(v)[k],
        v[j] == val,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    let l_len = l.len();
    
    while index < l_len
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> #[trigger] result[j] == l[j] + 1,
            index <= l_len,
        decreases l_len - index,
    {
        assert(0 <= index < l_len) by { 
            assert(index < l_len); 
        };
        proof { lemma_vec_index_in_bounds(l, index as int); }
        let val = l[index];
        assert(val + 1 <= i32::MAX);
        let old_result = result.clone();
        result.push(val + 1);
        index = index + 1;
        
        proof {
            assert forall|j: int| 0 <= j < index implies #[trigger] result[j] == l[j] + 1 by {
                if j < index - 1 {
                    assert(old_result[j] == l[j] + 1);
                    assert(result@ =~= old_result@.push(val + 1));
                    assert(result@[j] == old_result@[j]);
                    lemma_vec_indexing(result, j);
                    lemma_vec_indexing(old_result, j);
                } else {
                    assert(j == index - 1);
                    assert(result@[j] == val + 1);
                    assert(l@[j] == val);
                    lemma_vec_indexing(result, j);
                    lemma_vec_indexing(l, j);
                }
            };
        }
    }
    
    proof {
        lemma_vec_len(result);
        lemma_vec_len(l);
        assert(result@.len() == l@.len());
        assert forall|i: int| 0 <= i < l_len implies result[i] == l[i] + 1 by {
            assert(0 <= i < l_len);
            assert(result[i] == l[i] + 1);
        };
        assert(result@ =~= l@.map(|x| x + 1));
    }
    
    result
}
// </vc-code>

fn main() {}
}