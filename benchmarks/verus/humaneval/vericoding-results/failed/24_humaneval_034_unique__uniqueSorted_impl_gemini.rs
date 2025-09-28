// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique_sorted(s: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures 
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int, j: int| 0 <= k < j < result@.len() ==> result@[k] < result@[j],
            forall|k: int| 0 <= k < i ==> result@.contains(s@[k as int]),
            forall|x: i8| result@.contains(x) ==> s@.subrange(0, i as int).contains(x),
            i < s.len() && result@.len() > 0 ==> result@.last() <= s@[i as int],
        decreases s.len() - i
    {
        let current = s[i];
        if result.len() == 0 || current > result[result.len() - 1] {
            result.push(current);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}