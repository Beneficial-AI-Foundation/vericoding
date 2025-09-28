// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
proof fn triv() { }
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut result: Vec<nat> = Vec::new();

    while i < a1.len() || j < a2.len()
        invariant
            i <= a1.len(),
            j <= a2.len(),
            is_sorted(result@),
            result@.len() == i as int + j as int,
            result@.to_multiset() == a1@.take(i as int).to_multiset().add(a2@.take(j as int).to_multiset()),
            result@.len() == 0
                || (i < a1.len() ==> result@[result@.len() - 1] <= a1@[i as int])
                && (j < a2.len() ==> result@[result@.len() - 1] <= a2@[j as int]),
        decreases (a1.len() as int + a2.len() as int) - i as int - j as int
    {
        if i < a1.len() && (j == a2.len() || a1[i] <= a2[j]) {
            let x = a1[i];
            proof {
                if result@.len() > 0 {
                    assert(result@[result@.len() - 1] <= x);
                }
            }
            result.push(x);
            i += 1;
        } else {
            let y = a2[j];
            proof {
                if result@.len() > 0 {
                    assert(result@[result@.len() - 1] <= y);
                }
            }
            result.push(y);
            j += 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}