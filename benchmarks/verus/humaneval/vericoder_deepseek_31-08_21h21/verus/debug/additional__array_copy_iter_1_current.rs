use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_indexing<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s[i],
{
}

proof fn lemma_vec_indexing<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v[i] == v@[i],
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a@[j],
    {
        result.push(a[i]);
        proof {
            lemma_vec_indexing(&a, i as int);
            lemma_seq_indexing(a@, i as int);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}