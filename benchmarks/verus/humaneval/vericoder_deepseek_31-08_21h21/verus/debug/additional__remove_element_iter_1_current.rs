use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_split<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s = s.subrange(0, i) + s.subrange(i + 1, s.len()),
{
    assert(s.subrange(0, i) + s.subrange(i, i + 1) + s.subrange(i + 1, s.len()) == s);
    assert(s.subrange(i, i + 1) == Seq::empty().push(s[i]));
}

proof fn lemma_vec_to_seq_index<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@[i] == v[i as usize],
{
}

proof fn lemma_vec_to_seq_len<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len() as int,
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut j: usize = 0;
    
    while j < a.len()
        invariant
            j <= a.len(),
            result.len() == j - (if j > pos {1} else {0}),
            forall|k: int| 0 <= k < j && k != pos ==> result[k - (if k > pos {1} else {0})] == a[k as usize],
            forall|k: int| 0 <= k < result.len() ==> (k < pos ==> result[k] == a[k as usize]) && (k >= pos ==> result[k] == a[k as usize + 1]),
    {
        if j != pos {
            result.push(a[j]);
        }
        j = j + 1;
    }
    
    proof {
        lemma_vec_to_seq_len(&result);
        assert(result@.len() == a.len() as int - 1);
        
        let mut i: int = 0;
        while i < pos
            invariant
                0 <= i <= pos,
                forall|k: int| 0 <= k < i ==> result@[k] == a@[k],
        {
            lemma_vec_to_seq_index(&result, i);
            lemma_vec_to_seq_index(a, i);
            assert(result[i as usize] == a[i as usize]);
            i = i + 1;
        }
        
        let mut i: int = pos;
        while i < result@.len()
            invariant
                pos <= i <= result@.len(),
                forall|k: int| pos <= k < i ==> result@[k] == a@[k + 1],
        {
            lemma_vec_to_seq_index(&result, i);
            lemma_vec_to_seq_index(a, i + 1);
            assert(result[i as usize] == a[(i + 1) as usize]);
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}