// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): assert int index fits in usize */
proof fn assert_index_cast(i: int, n: usize)
    requires 0 <= i && i < n as int
{
    assert((i as usize) < n);
}

// </vc-helpers>

// <vc-spec>
fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate over s, push elements into result, invariant uses spec int indexing */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j] == s[j],
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}