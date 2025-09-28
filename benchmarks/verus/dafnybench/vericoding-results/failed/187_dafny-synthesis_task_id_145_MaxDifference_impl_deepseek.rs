use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn max_diff_proof(a: Seq<i32>, max_val: i32, min_val: i32, i: int)
    requires
        0 <= i < a.len(),
        forall|k: int| 0 <= k < i ==> a[k] <= max_val,
        forall|k: int| 0 <= k < i ==> min_val <= a[k],
        max_val >= a[0],
        min_val <= a[0],
    ensures
        max_val >= a[i],
        min_val <= a[i],
{
}

proof fn max_diff_lemma(a: Seq<i32>, max_val: i32, min_val: i32)
    requires
        a.len() > 1,
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max_val,
        forall|i: int| 0 <= i < a.len() ==> min_val <= a[i],
    ensures
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= max_val - min_val,
{
    assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() implies a[i] - a[j] <= max_val - min_val by {
        assert(a[i] <= max_val);
        assert(min_val <= a[j]);
    };
}
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  let mut max_val = a[0];
  let mut min_val = a[0];
  let mut i: usize = 1;
  while i < a.len()
    decreases a.len() - i
    invariant
        i <= a.len(),
        forall|k: int| 0 <= k < i ==> a[k] <= max_val,
        forall|k: int| 0 <= k < i ==> min_val <= a[k],
        max_val >= a[0],
        min_val <= a[0],
  {
      if a[i] > max_val {
          max_val = a[i];
      }
      if a[i] < min_val {
          min_val = a[i];
      }
      assert forall|k: int| 0 <= k < i+1 implies a[k] <= max_val by {
          if k < i {
              assert(a[k] <= max_val);
          } else {
              assert(k == i);
              assert(a[i] <= max_val);
          }
      };
      assert forall|k: int| 0 <= k < i+1 implies min_val <= a[k] by {
          if k < i {
              assert(min_val <= a[k]);
          } else {
              assert(k == i);
              assert(min_val <= a[i]);
          }
      };
      i = i + 1;
  }
  proof {
      max_diff_lemma(a@, max_val, min_val);
  }
  max_val - min_val
}
// </vc-code>

fn main() {
}

}