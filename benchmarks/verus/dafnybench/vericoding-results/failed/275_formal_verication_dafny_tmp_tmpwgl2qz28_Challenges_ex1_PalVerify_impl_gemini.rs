// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added a lemma to bridge the gap between the good-trigger invariant and the bad-trigger ensures clause */
spec fn is_palindrome_prefix(s: Seq<char>, i: int) -> bool {
    forall|j: int, k: int| #![trigger s[j], s[k]]
        0 <= j < i && k == s.len() - 1 - j ==> s[j] == s[k]
}

proof fn lemma_palindrome_bridge(s: Seq<char>)
    requires is_palindrome_prefix(s, s.len()/2 as int)
    ensures forall|i: int| 0 <= i < s.len()/2 ==> s[i] == s[s.len() - 1 - i]
{
}
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> (forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]),
            yn == false ==> (exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change to logic, which relies on a new helper lemma to pass verification */
    let n = a.len();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            i as int <= (n as int) / 2,
            is_palindrome_prefix(a.view(), i as int),
        decreases (n / 2) - i
    {
        if a[i] != a[n - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    lemma_palindrome_bridge(a.view());
    return true;
}
// </vc-code>

}
fn main() {}