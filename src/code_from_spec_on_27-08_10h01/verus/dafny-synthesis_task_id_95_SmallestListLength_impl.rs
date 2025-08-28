use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn min_length(s: Seq<Seq<int>>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 {
        s[0].len() as int
    } else {
        if s[0].len() <= min_length(s.subrange(1, s.len() as int)) {
            s[0].len() as int
        } else {
            min_length(s.subrange(1, s.len() as int))
        }
    }
}

proof fn lemma_min_length_is_minimum(s: Seq<Seq<int>>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> min_length(s) <= s[i].len()
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: trivial
    } else {
        lemma_min_length_is_minimum(s.subrange(1, s.len() as int));
        // The minimum is either s[0].len() or the minimum of the rest
        if s[0].len() <= min_length(s.subrange(1, s.len() as int)) {
            // min_length(s) == s[0].len()
        } else {
            // min_length(s) == min_length(s.subrange(1, s.len() as int))
        }
    }
}

proof fn lemma_min_length_exists(s: Seq<Seq<int>>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && min_length(s) == s[i].len()
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: min_length(s) == s[0].len()
    } else {
        lemma_min_length_exists(s.subrange(1, s.len() as int));
        if s[0].len() <= min_length(s.subrange(1, s.len() as int)) {
            // min_length(s) == s[0].len(), so i = 0 works
        } else {
            // min_length(s) == min_length(s.subrange(1, s.len() as int))
            // From the recursive call, there exists j such that
            // min_length(s.subrange(1, s.len() as int)) == s.subrange(1, s.len() as int)[j].len()
            // This means s[j+1].len() == min_length(s)
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && v == #[trigger] s[i].len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut min_len_exec = s@[0].len();
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> min_len_exec as int <= s@[j].len(),
            exists|j: int| 0 <= j < i && min_len_exec as int == s@[j].len(),
    {
        if s@[i].len() < min_len_exec {
            min_len_exec = s@[i].len();
        }
        i = i + 1;
    }
    min_len_exec as int
}
// </vc-code>

fn main() {
}

}