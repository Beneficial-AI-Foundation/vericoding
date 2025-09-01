use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_reverse_property(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s.reverse()[s.len() - 1 - i],
{
    assert(s.reverse()[i] == s[s.len() - 1 - i]);
    assert(s.reverse()[s.len() - 1 - i] == s[i]);
}

proof fn forall_reverse_equivalence(s: Seq<char>)
    ensures
        (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[s.len() - 1 - i]) == (s == s.reverse()),
{
    assert(s.reverse().reverse() == s);
    assert(forall|i: int| 0 <= i < s.len() ==> #[trigger] s.reverse()[i] == s.reverse()[s.reverse().len() - 1 - i]);
    lemma_reverse_property(s, 0);
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let seq = text@;
    let mut i = 0;
    let n = seq.len();
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] seq[j] == seq[n - 1 - j],
    {
        proof {
            lemma_reverse_property(seq, i);
        }
        i = i + 1;
    }
    i == n
}
// </vc-code>

fn main() {}
}