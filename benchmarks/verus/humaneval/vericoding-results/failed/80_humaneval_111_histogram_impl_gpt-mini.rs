// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): update counts for prefix by inserting/incrementing value */
lemma count_prefix_update(m: BiggestMap, a: Vec<i8>, idx: int)
    requires
        0 <= idx && idx < a@.len(),
        forall|i: int| 0 <= i < idx ==> m.dom().contains(a@[i] as int),
        forall|i: int| 0 <= i < idx ==> m[a@[i] as int] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == a@[i] as int).len(),
    ensures
        let v = a@[idx] as int,
        let m2 = if m.dom().contains(v) { m.insert(v, m[v] + 1) } else { m.insert(v, 1) },
        forall|i: int| 0 <= i < idx+1 ==> m2.dom().contains(a@[i] as int) && m2[a@[i] as int] == Set::new(|j: int| 0 <= j < idx+1 && a@[j] as int == a@[i] as int).len(),
{
    proof {
        let v = a@[idx] as int;
        let m2 = if m.dom().contains(v) { m.insert(v, m[v] + 1) } else { m.insert(v, 1) };
        // show the forall property for an arbitrary index i
        fix i;
        assume H_i: 0 <= i && i < idx+1;
        if i < idx {
            // use the preconditions for indices < idx
            assert(m.dom().contains(a@[i] as int));
            if a@[i] as int == v {
                // when equal to v, the updated map increments the count
                assert(m.dom().contains(v));
                assert(m2[a@[i] as int] == m[a@[i] as int] + 1);
                assert(m[a@[i] as int] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == a@[i] as int).len());
                assert(m2[a@[i] as int] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == a@[i] as int).len() + 1);
                assert(m2[a@[i] as int] == Set::new(|j: int| 0 <= j < idx+1 && a@[j] as int == a@[i] as int).len());
                assert(m2.dom().contains(a@[i] as int));
            } else {
                // when different, value remains the same
                assert(m2[a@[i] as int] == m[a@[i] as int]);
                assert(m[a@[i] as int] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == a@[i] as int).len());
                assert(m2[a@[i] as int] == Set::new(|j: int| 0 <= j < idx+1 && a@[j] as int == a@[i] as int).len());
                assert(m2.dom().contains(a@[i] as int));
            }
        } else {
            // i == idx: the new map contains v with the correct count
            assert(i == idx);
            assert(m2.dom().contains(v));
            if m.dom().contains(v) {
                assert(m2[v] == m[v] + 1);
                assert(m[v] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == v).len());
                assert(m2[v] == Set::new(|j: int| 0 <= j < idx && a@[j] as int == v).len() + 1);
                assert(m2[v] == Set::new(|j: int| 0 <= j < idx+1 && a@[j] as int == v).len());
            } else {
                assert(m2[v] == 1);
                assert(m2[v] == Set::new(|j: int| 0 <= j < idx+1 && a@[j] as int == v).len());
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a@.len() && biggest.dom().contains(a@[i] as int) ==>
    #[trigger] biggest[a@[i] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[i] as int).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build frequency map incrementally using helper */
    let mut m: BiggestMap = Map::empty();
    let n: int = a@.len() as int;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            forall|j: int| 0 <= j < i ==> m.dom().contains(a@[j] as int) && m[a@[j] as int] == Set::new(|k: int| 0 <= k < i && a@[k] as int == a@[j] as int).len(),
        decreases n - i
    {
        let old_m = m;
        let v: int = a@[i] as int;
        let new_m = if old_m.dom().contains(v) {
            old_m.insert(v, old_m[v] + 1)
        } else {
            old_m.insert(v, 1)
        };
        m = new_m;
        // re-establish the invariant for the extended prefix
        proof {
            count_prefix_update(old_m, a, i);
        }
        i = i + 1;
    }
    m
}
// </vc-code>


}

fn main() {}