// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed preconditions by using indexing instead of subrange */
fn equals_at(s: &Vec<char>, start: usize, substr: &Vec<char>) -> (res: bool)
    requires
        start + substr.len() <= s.len(),
    ensures
        res <==> forall|i: int| 0 <= i < substr@.len() ==> s@[start + i] == substr@[i]
{
    let mut i = 0;
    while i < substr.len()
        invariant
            0 <= i <= substr@.len(),
            forall|j: int| 0 <= j < i ==> s@[start + j] == substr@[j],
        decreases substr@.len() - i
    {
        if s[start + i] != substr[i] {
            return false;
        }
        i += 1;
    }
    true
}

// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing misplaced attribute */
    if substr.len() > s.len() {
        return 0;
    }
    let mut count: usize = 0;
    let mut i: usize = 0;
    let end: usize = s.len() - substr.len();
    while i <= end
        invariant
            0 <= i <= end + 1,
            count == Set::new(|k: int| 0 <= k < i as int && forall|j: int| 0 <= j < substr@.len() ==> s@[k + j] == substr@[j]).len() as usize,
        decreases (end as int - i as int) + 1
    {
        if equals_at(&s, i, &substr) {
            count += 1;
        }
        i += 1;
    }
    count
}

// </vc-code>


}

fn main() {}