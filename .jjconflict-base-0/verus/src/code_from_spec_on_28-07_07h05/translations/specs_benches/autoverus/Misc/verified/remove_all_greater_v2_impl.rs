use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The proof is automatic - Verus can prove these properties about sequence push
}

//IMPL remove_all_greater
/* code modified by LLM (iteration 3): added lemma to prove contains property is preserved after push */
proof fn lemma_contains_preserved<T>(seq: Seq<T>, new_elem: T, elem: T)
    ensures
        seq.contains(elem) ==> seq.push(new_elem).contains(elem),
{
    if seq.contains(elem) {
        let idx = seq.index_of(elem);
        assert(seq.push(new_elem)[idx] == elem);
    }
}

pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    /* code modified by LLM (iteration 1): added explicit type annotation Vec<i32> to fix compilation error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            /* code modified by LLM (iteration 4): fixed syntax error in forall statement */
            proof {
                forall |k: int| 0 <= k < i && v[k] <= e 
                ensures result@.push(v[i]).contains(v[k])
                {
                    if result@.contains(v[k]) {
                        lemma_contains_preserved(result@, v[i], v[k]);
                    }
                }
            }
            result.push(v[i]);
        }
        i += 1;
    }
    
    result
}
}