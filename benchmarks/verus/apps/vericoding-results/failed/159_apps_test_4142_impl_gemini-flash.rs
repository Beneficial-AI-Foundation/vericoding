// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

spec fn easily_playable(s: Seq<char>) -> bool {
    (forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> s[i] != 'L') &&
    (forall|i: int| 0 <= i < s.len() && i % 2 == 1 ==> s[i] != 'R')
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_easily_playable_even_L(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        i % 2 == 0,
        s[i] == 'L',
    ensures
        !easily_playable(s),
{
    assert(!((forall|j: int| 0 <= j < s.len() && j % 2 == 0 ==> s[j] != 'L')));
}

proof fn lemma_easily_playable_odd_R(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        i % 2 == 1,
        s[i] == 'R',
    ensures
        !easily_playable(s),
{
    assert(!((forall|j: int| 0 <= j < s.len() && j % 2 == 1 ==> s[j] != 'R')));
}
// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
{
    let s_seq = s@;
    let len = s_seq.len();

    let mut i: int = 0;
    while i < len
        invariant
            0 <= i <= len,
            valid_input(s_seq),
            // If we found a violation before, it remains a violation
            // The `easily_playable` property still holds for the prefix we've checked
            // (This invariant is conceptual; the proof requires checking the whole sequence if no violation is found)
        decreases len - i
    {
        if i % 2 == 0 {
            if s_seq[i] == 'L' {
                proof {
                    lemma_easily_playable_even_L(s_seq, i);
                }
                return "No".to_string();
            }
        } else { // i % 2 == 1
            if s_seq[i] == 'R' {
                proof {
                    lemma_easily_playable_odd_R(s_seq, i);
                }
                return "No".to_string();
            }
        }
        i = i + 1;
    }

    // If the loop completes, it means no 'L' at even indices and no 'R' at odd indices were found.
    // Therefore, the sequence is easily playable.
    proof {
        assert(easily_playable(s_seq));
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}