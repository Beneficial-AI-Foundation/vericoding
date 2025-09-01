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
}
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
    
    while index < l.len()
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> #[trigger] result[j] == l[j] + 1,
            index <= l.len(),
        decreases l.len() - index,
    {
        result.push(l[index] + 1);
        index = index + 1;
    }
    
    proof {
        lemma_vec_len(result);
        lemma_vec_len(l);
    }
    
    result
}
// </vc-code>

fn main() {}
}