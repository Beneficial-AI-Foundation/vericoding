use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::set::*;

proof fn lemma_subrange_equality(text: &str, pattern: &str, i: nat)
    requires
        i + pattern@.len() <= text@.len(),
        text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@,
    ensures
        forall|j: nat| j < pattern@.len() ==> text@[i + j] == pattern@[j]
{
    let text_len = text@.len();
    let pat_len = pattern@.len();
    assert forall|j: nat| j < pat_len implies text@[i + j] == pattern@[j] by {
        assert(i + j < text_len);
        assert(text@.subrange(i as int, (i + pat_len) as int)[j as int] == pattern@[j]);
        assert(text@.subrange(i as int, (i + pat_len) as int)[j as int] == text@[i + j]);
    };
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_all_occurrences(text: &str, pattern: &str) -> (offsets: Ghost<Set<nat>>)
    ensures 
        forall|i: nat| offsets@.contains(i) ==> i + pattern@.len() <= text@.len(),
        forall|i: nat| 0 <= i && i + pattern@.len() <= text@.len() 
                      ==> (text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@) == offsets@.contains(i)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_all_occurrences(text: &str, pattern: &str) -> (offsets: Ghost<Set<nat>>)
    ensures 
        forall|i: nat| offsets@.contains(i) ==> i + pattern@.len() <= text@.len(),
        forall|i: nat| 0 <= i && i + pattern@.len() <= text@.len() 
                      ==> (text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@) == offsets@.contains(i)
{
    let mut result = Set::empty();
    let text_len = text@.len();
    let pat_len = pattern@.len();
    
    if pat_len == 0 {
        let mut i: nat = 0;
        while i <= text_len
            invariant
                0 <= i <= text_len + 1,
                forall|j: nat| j < i ==> result.contains(j),
                forall|j: nat| j >= i ==> !result.contains(j),
        {
            result = result.insert(i);
            i = i + 1;
        }
        return Ghost(result);
    }
    
    let mut i: nat = 0;
    while i + pat_len <= text_len
        invariant
            0 <= i <= text_len,
            i + pat_len <= text_len + 1,
            forall|j: nat| j < i && j + pat_len <= text_len ==> 
                result.contains(j) == (text@.subrange(j as int, (j + pat_len) as int) == pattern@),
            forall|j: nat| j >= i ==> !result.contains(j),
    {
        if text@.subrange(i as int, (i + pat_len) as int) == pattern@ {
            proof {
                lemma_subrange_equality(text, pattern, i);
            }
            result = result.insert(i);
        }
        i = i + 1;
    }
    Ghost(result)
}
// </vc-code>

fn main() {}

}