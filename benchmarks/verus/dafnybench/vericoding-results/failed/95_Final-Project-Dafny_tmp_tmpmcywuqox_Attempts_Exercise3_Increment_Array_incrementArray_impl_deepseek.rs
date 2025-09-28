use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_vec_len_unchanged<T>(v: Vec<T>)
    ensures
        v.len() == v.len(),
{
}

proof fn lemma_vec_index_unchanged<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v[i] == v[i],
{
}

proof fn lemma_seq_index_cast(s: Seq<i32>, i: usize)
    requires
        0 <= i < s.len(),
    ensures
        s[i as int] == s[i],
{
}
// </vc-helpers>

// <vc-spec>
fn increment_array(a: &mut Vec<i32>)
  requires old(a).len() > 0,
  ensures 
      a.len() == old(a).len(),
      forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.len() == old(a)@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == old(a)@[j] + 1,
            forall|j: int| i <= j < a@.len() ==> a@[j] == old(a)@[j],
    {
        let old_val = a[i];
        a[i] = old_val + 1;
        
        proof { lemma_seq_index_cast(a@, i); }
        proof { lemma_seq_index_cast(old(a)@, i); }
        
        assert(a@[i] == old(a)@[i] + 1);
        i = i + 1;
    }
    assert forall|k: int| 0 <= k < a@.len() implies a@[k] == old(a)@[k] + 1 by {
        assert(0 <= k < a@.len());
    };
}
// </vc-code>

fn main() {}

}