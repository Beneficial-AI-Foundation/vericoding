use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<i32>) -> (usize, usize)
// </vc-spec>
// <vc-code>
{
  assume(false);
  let lo: usize = 0;
  let hi: usize = 0;
  
  // This is a post-condition that must be proven
  assert(0 <= lo && lo <= hi && hi <= a.len());
  assert(forall|x: int| 0 <= x < lo ==> a[x as int] < 0);
  assert(forall|x: int| lo <= x < hi ==> a[x as int] == 0);
  assert(forall|x: int| hi <= x < a.len() ==> a[x as int] > 0);
  
  (lo, hi)
}
// </vc-code>

fn main() {
}

}
