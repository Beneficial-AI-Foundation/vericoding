use vstd::prelude::*;

verus! {

// <vc-helpers>
fn increment_array_rec(a: &mut Vec<i32>, orig: Vec<i32>, i: nat)
    requires i <= a.len(),
    requires forall |k: nat| k < i ==> a[k] == orig[k] + 1,
    requires forall |k: nat| i <= k && k < a.len() ==> a[k] == orig[k],
    ensures forall |k: nat| k < a.len() ==> a[k] == orig[k] + 1,
    ensures a.len() == old(a).len(),
    decreases a.len() - i
{
    if i < a.len() {
        let v: i32 = a[i];
        a[i] = v + 1;
        // The verifier can see that for k < i+1 the updated a[k] == orig[k] + 1:
        // - for k < i it holds by the precondition,
        // - for k == i it holds because we just set a[i] = orig[i] + 1.
        increment_array_rec(a, orig, i + 1);
    } else {
        // nothing to do
    }
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
    let n: nat = a.len();
    let orig: Vec<i32> = a.clone();

    // initial invariants for recursion:
    // for i = 0, the two preconditions of increment_array_rec hold:
    //   forall k < 0 ==> ...  (vacuous)
    //   forall 0 <= k < a.len() ==> a[k] == orig[k]  (true because orig is a.clone())
    increment_array_rec(a, orig, 0);

    proof {
        assert(a.len() == n);
        assert(forall |k: nat| k < n ==> a[k] == orig[k] + 1);
    }
}
// </vc-code>

fn main() {}

}