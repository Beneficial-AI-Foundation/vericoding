use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == in_array(a@, x),
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != x,
    {
        if a[i] == x {
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn lemma_not_in_array_means_all_different(a: Seq<i32>, x: i32)
    requires !in_array(a, x)
    ensures forall|k: int| 0 <= k < a.len() ==> a[k] != x
{
}

proof fn lemma_vec_push_preserves_uniqueness(v: &Vec<i32>, x: i32)
    requires forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] != v@[j],
        !in_array(v@, x)
    ensures forall|i: int, j: int| 0 <= i < j < (v@.push(x)).len() ==> (v@.push(x))[i] != (v@.push(x))[j]
{
    let new_seq = v@.push(x);
    let old_len = v@.len();
    let new_len = new_seq.len();
    
    assert(new_len == old_len + 1);
    assert(new_seq[old_len] == x);
    
    assert forall|i: int, j: int| 0 <= i < j < new_len implies new_seq[i] != new_seq[j] by {
        if j == old_len {
            assert(new_seq[j] == x);
            if i < old_len {
                assert(new_seq[i] == v@[i]);
                assert(v@[i] != x) by {
                    lemma_not_in_array_means_all_different(v@, x);
                }
            }
        } else {
            assert(i < j < old_len);
            assert(new_seq[i] == v@[i]);
            assert(new_seq[j] == v@[j]);
            assert(v@[i] != v@[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c@[k]) && !in_array(b@, c@[k]),
            forall|p: int, q: int| 0 <= p < q < c.len() ==> c@[p] != c@[q],
    {
        if in_array_exec(b, a[i as usize]) {
            i = i + 1;
            continue;
        }
        
        if !in_array_exec(&c, a[i as usize]) {
            proof {
                lemma_vec_push_preserves_uniqueness(&c, a[i]);
            }
            c.push(a[i as usize]);
        }
        
        i = i + 1;
    }
    
    c
}
// </vc-code>

fn main() {}
}