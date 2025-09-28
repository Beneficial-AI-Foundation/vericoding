// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invalid forall syntax from requires/ensures to implies */
proof fn lemma_finish_symmetric_check(s: Seq<i32>)
    requires
        forall|i: int| 0 <= i < s.len() / 2 ==> s[i] == s[s.len() - 1 - i],
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i],
{
    let n = s.len() as int;
    forall|i: int| 0 <= i < n implies #[trigger] s[i] == s[n - 1 - i] by {
        if i < n / 2 {
            // This case is directly covered by the requires clause of the lemma.
        } else {
            let j = n - 1 - i;
            // For i >= n/2, j is in the first half, so the precondition applies to j.
            assert(s[j] == s[n - 1 - j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): resubmitting with fixed helper function */
{
    let mut i: usize = 0;
    let n = a.len();
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            a.len() == n,
            forall|j: int| 0 <= j < i ==> a[j] == a[n - 1 - j],
        decreases (n as int) / 2 - (i as int)
    {
        if a[i] != a[n - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    lemma_finish_symmetric_check(a@);
    return true;
}
// </vc-code>

}
fn main() {}