// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Removed the problematic invariant about overflow and a redundant assertion. */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == old(a)@[j] + 1,
            forall|j: int| i <= j < a.len() ==> a@[j] == old(a)@[j],
        decreases a.len() - i
    {
        a.set(i, a[i] + 1);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}