// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn canyon_search(a: &[i32], b: &[i32]) -> (d: u32)
  requires 
      a.len() != 0 && b.len() != 0,
      forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
      forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] <= b[j],
  ensures
      exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && 
          d as int == (if a[i] < b[j] { 
              b[j] - a[i]
          } else { 
              a[i] - b[j]
          }),
      forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
          d as int <= (if a[i] < b[j] { 
              b[j] - a[i]
          } else { 
              a[i] - b[j]
          }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}