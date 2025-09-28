use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::seq::Seq;

// Needed to convert Vec to Seq for ghost comparisons
// This is a common pattern when dealing with Vecs in specs
proof fn vec_to_seq<T: Copy>(v: &Vec<T>) -> Seq<T>
    ensures
        v.len() == result.len(),
        forall|i: int| #![trigger result.index(i)] 0 <= i && i < v.len() as int ==> result.index(i) == v.index(i),
{
    let mut s = Seq::new(v.len() as nat, |i: nat| v[i as usize]);
    s
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
    let old_a_len = old(a).len();
    let original_a = old(a).to_vec(); // Capture the old state of `a` as a new Vec
    let original_a_seq = vec_to_seq(&original_a); // Convert to Seq for specification

    assert(a.len() == old_a_len);

    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old_a_len,
            0 <= i as int && i as int <= a.len() as int,
            forall|j: int| 0 <= j && j < i as int ==> a[j as usize] == original_a_seq.index(j) + 1,
            forall|j: int| i as int <= j && j < a.len() as int ==> a[j as usize] == original_a_seq.index(j),
    {
        a.set(i, a[i] + 1);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}