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

proof fn lemma_palindrome_loop(seq: Seq<char>, i: nat, n: nat)
    requires
        i <= n / 2,
        forall|j: int| 0 <= j < i ==> #[trigger] seq[j] == seq[n - 1 - j],
    ensures
        forall|j: int|
            0 <= j < i ==> #[trigger] seq[j] == seq[n - 1 - j],
{
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
    let mut i: nat = 0;
    let n = seq.len() as nat;
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] seq@[j] == seq@[n - 1 - j],
    {
        lemma_palindrome_loop(seq, i, n);
        assert(seq@[i] == seq@[n - 1 - i]);
        i = i + 1;
    }
    if n > 0 {
        assert(forall|i: int| 0 <= i < n ==> #[trigger] seq@[i] == seq@[n - 1 - i]);
    } else {
        assert(forall|i: int| 0 <= i < 0 ==> false);
    }
    forall|i: int| 0 <= i < n ==> #[trigger] seq@[i] == seq@[n - 1 - i]
}
// </vc-code>

fn main() {}
}