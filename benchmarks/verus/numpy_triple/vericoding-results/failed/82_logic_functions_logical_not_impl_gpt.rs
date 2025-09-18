// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate for checking zero */
spec fn is_zero_f64(x: f64) -> bool { x == 0.0 }

/* helper modified by LLM (iteration 5): lemma that pushing onto a sequence preserves existing prefix indices */
proof fn seq_push_preserves_prefix<A>(s: Seq<A>, a: A, j: int)
    requires 0 <= j && j < s.len()
    ensures s.push(a)[j] == s[j]
{ }

/* helper modified by LLM (iteration 5): lemma that the last element after push is the pushed value */
proof fn seq_push_last<A>(s: Seq<A>, a: A)
    ensures s.push(a)[s.len()] == a
{ }
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced incorrect assert_forall_by usage; added proof steps without requires/ensures inside closures */
    let n = x.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x@[j] == 0.0)
        decreases n - i
    {
        assert(i < n);
        assert(n == x.len());
        assert(i < x.len());

        let ghost old_view: Seq<bool> = result@;
        let ghost old_i: int = i as int;
        proof {
            // Relate old_view to current result view and collect property from the invariant
            assert(result@ == old_view);
            assert(forall|j: int| 0 <= j && j < old_i ==> old_view[j] == (x@[j] == 0.0));
            assert_forall_by(|j: int| {
                if 0 <= j && j < old_i {
                    assert(result@ == old_view);
                    assert(result@[j] == old_view[j]);
                    assert(result@[j] == (x@[j] == 0.0));
                }
            });
        }

        let b = x[i] == 0.0;
        result.push(b);

        proof {
            // After push: result@ == old_view.push(b)
            assert(result@ == old_view.push(b));
            assert(result.len() as int == old_i + 1);
            assert(old_view.len() == old_i);

            // Show prefix is preserved
            assert(forall|j: int| 0 <= j && j < old_i ==> result@[j] == old_view[j]);
            assert_forall_by(|j: int| {
                if 0 <= j && j < old_i {
                    assert(j < old_view.len());
                    assert(result@[j] == old_view.push(b)[j]);
                    seq_push_preserves_prefix::<bool>(old_view, b, j);
                    assert(old_view.push(b)[j] == old_view[j]);
                }
            });

            // Show last element is b
            assert(result@[old_i] == old_view.push(b)[old_i]);
            assert(old_view.push(b)[old_i] == b);

            // Establish the loop invariant for the next iteration
            assert(forall|j: int| 0 <= j && j < old_i + 1 ==> result@[j] == (x@[j] == 0.0));
            assert_forall_by(|j: int| {
                if 0 <= j && j < old_i {
                    // From prefix preservation and prior invariant
                    assert(result@[j] == old_view[j]);
                    assert(old_view[j] == (x@[j] == 0.0));
                } else {
                    assert(0 <= j && j < old_i + 1);
                    assert(!(j < old_i));
                    assert(j >= old_i);
                    assert(j == old_i);
                    assert(result@[old_i] == b);
                    assert(b == (x@[old_i] == 0.0));
                }
            });
        }

        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}