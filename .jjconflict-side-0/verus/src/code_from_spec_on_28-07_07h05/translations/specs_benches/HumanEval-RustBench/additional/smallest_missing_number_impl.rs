use vstd::prelude::*;

verus! {

//IMPL smallest_missing_number
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
{
    let mut i = 0;
    let mut expected = 0;
    
    /* code modified by LLM (iteration 1): added explicit trigger annotation for quantifier */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            0 <= expected,
            #[trigger] forall|k: int| 0 <= k < expected ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
            i > 0 ==> s[i - 1] >= expected,
            forall|j: int| 0 <= j < i ==> s[j] < expected || s[j] == expected,
        decreases s.len() - i
    {
        if s[i] == expected {
            expected = expected + 1;
        }
        i = i + 1;
    }
    
    expected
}

fn main() {}
}