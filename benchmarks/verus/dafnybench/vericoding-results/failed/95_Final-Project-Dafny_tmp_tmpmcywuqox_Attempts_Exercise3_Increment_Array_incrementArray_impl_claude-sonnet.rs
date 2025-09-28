use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish bounds for preventing overflow
proof fn lemma_i32_bounds()
    ensures forall|x: i32| x < i32::MAX ==> x + 1 <= i32::MAX
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
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old(a).len(),
            forall|j: int| #![auto] 0 <= j < i ==> a[j] == old(a)[j] + 1,
            forall|j: int| #![auto] i <= j < a.len() ==> a[j] == old(a)[j],
            forall|j: int| #![auto] 0 <= j < a.len() ==> old(a)[j] < i32::MAX,
        decreases a.len() - i,
    {
        let old_val = a[i];
        assert(old_val == old(a)[i as int]);
        assert(old_val < i32::MAX);
        a.set(i, old_val + 1);
        
        proof {
            assert(a[i as int] == old(a)[i as int] + 1);
            assert(forall|j: int| #![auto] 0 <= j < i ==> a[j] == old(a)[j] + 1);
            assert(forall|j: int| #![auto] (i + 1) <= j < a.len() ==> a[j] == old(a)[j]);
        }
        
        i += 1;
        
        assert(forall|j: int| #![auto] 0 <= j < i ==> a[j] == old(a)[j] + 1);
    }
}
// </vc-code>

fn main() {}

}