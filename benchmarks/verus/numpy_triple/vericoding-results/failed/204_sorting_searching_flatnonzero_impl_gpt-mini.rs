// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that usize casts to int are nonnegative */
proof fn lemma_usize_cast_nonneg(n: usize)
    ensures
        (n as int) >= 0,
{
}

/* helper modified by LLM (iteration 5): lemma relating Vec.get to the specification view */
proof fn lemma_vec_get_eq_view(v: &Vec<f64>, i: usize)
    requires
        i < v.len(),
    ensures
        match v.get(i) { Some(x) => *x == v@.[i as int], None => false },
{
    // The runtime element at index i equals the specification view at i
    // Proof is via the correspondence between Vec and its view
    // Use an assertion that the get yields the same value as the spec-indexing
    let opt = v.get(i);
    match opt {
        Some(x) => {
            // show that the spec view element equals the runtime reference
            assert(*x == v@.[i as int]);
        }
        None => {
            // This branch is impossible because of the requires clause
            assert(false);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterate using Vec::get to avoid direct indexing preconditions and maintain invariants relating res to a@ */
  let n = a.len();
  let mut res: Vec<usize> = Vec::new();
  let mut i: usize = 0;
  while i < n
      invariant
          forall|k: int| 0 <= k < (res@.len() as int) ==> a@[res@[k] as int] != 0.0,
          forall|k: int| 0 <= k < (res@.len() as int) ==> (res@[k] as int) < (i as int),
          forall|j: int| 0 <= j && j < (i as int) && a@[j] != 0.0 ==> exists|k: int| 0 <= k && k < (res@.len() as int) && (res@[k] as int) == j,
      decreases n - i
  {
      match a.get(i) {
          Some(x) => {
              if *x != 0.0 {
                  // connect runtime observation to the specification using helper lemma
                  proof {
                      lemma_vec_get_eq_view(&a, i);
                      assert(a@[i as int] == *x);
                  }
                  res.push(i);
              }
          }
          None => {
              // This case cannot happen because i < n and n == a.len()
          }
      }
      i = i + 1;
  }
  res
}
// </vc-code>

}
fn main() {}