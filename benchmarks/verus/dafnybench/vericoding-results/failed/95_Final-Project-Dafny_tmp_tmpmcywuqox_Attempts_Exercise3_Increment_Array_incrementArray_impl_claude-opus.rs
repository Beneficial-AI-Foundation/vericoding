use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let n = a.len();
    let mut i: usize = 0;
    let ghost old_a = a@;
    
    while i < n
        invariant
            a.len() == n,
            n == old_a.len(),
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> a@[j] == old_a[j] + 1,
            forall|j: int| i <= j < n ==> a@[j] == old_a[j],
    {
        let val = a[i];
        a.set(i, val + 1);
        
        assert(a@[i as int] == old_a[i as int] + 1);
        assert(forall|j: int| 0 <= j < i ==> a@[j] == old_a[j] + 1);
        assert(forall|j: int| i < j < n ==> a@[j] == old_a[j]);
        
        i = i + 1;
    }
    
    assert(i == n);
    assert(forall|j: int| 0 <= j < n ==> a@[j] == old_a[j] + 1);
}
// </vc-code>

fn main() {}

}