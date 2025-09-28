// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adjusted lemma to properly establish equivalence for the specific sequence map from i8 to int */
proof fn lemma_i8_monotonic_equiv(l: Seq<i8>)
    ensures
        l.len() <= 1 ||
        (
            (forall|i: nat| i < l.len() - 1 ==> l[i] <= l[i+1]) ==
            (forall|i: nat| i < l.len() - 1 ==> (l[i] as int) <= (l[i+1] as int))
        ),
        l.len() <= 1 ||
        (
            (forall|i: nat| i < l.len() - 1 ==> l[i] >= l[i+1]) ==
            (forall|i: nat| i < l.len() - 1 ==> (l[i] as int) >= (l[i+1] as int))
        )
{
}

// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assert statement with parentheses, adjusted proof block to correctly assert equivalence using the lemma for mapped sequence, and ensured consistent use of nat in invariants */
    if l.len() <= 1 {
        return true;
    }
    let mut increasing = true;
    let mut decreasing = true;
    let mut i: usize = 0;
    while i < l.len() - 1
        invariant
            i <= l.len() - 1,
            increasing == (forall|j: nat| j < i ==> l@[j] <= l@[j+1]),
            decreasing == (forall|j: nat| j < i ==> l@[j] >= l@[j+1])
        decreases (l.len() - i) as nat
    {
        if l[i] > l[i + 1] {
            increasing = false;
        }
        if l[i] < l[i + 1] {
            decreasing = false;
        }
        i += 1;
    }
    proof {
        let s = l@.map(|_, x: i8| x as int);
        lemma_i8_monotonic_equiv(l@);
        assert(increasing == (forall|j: nat| j < l.len() - 1 ==> s[j] <= s[j+1])) by {
            // By lemma, equivalence holds
        };
        assert(decreasing == (forall|j: nat| j < l.len() - 1 ==> s[j] >= s[j+1])) by {
            // By lemma, equivalence holds
        };
        assert((increasing || decreasing) == monotonic(s));
    }
    increasing || decreasing
}

// </vc-code>


}

fn main() {}