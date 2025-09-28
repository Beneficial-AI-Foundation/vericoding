// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_output(names: Seq<&str>, output: Seq<&str>) -> bool {
    output.len() == names.len() &&
    forall|i: int| 0 <= i < names.len() ==> 
        output[i] == (if exists|j: int| 0 <= j < i && names[j] == names[i] { "YES" } else { "NO" })
}
// </vc-preamble>

// <vc-helpers>
// 
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed indexing in invariant to use sequence view */
{
    let mut output = Vec::new();
    for i in 0..names.len()
        invariant
            output.len() == i,
            forall |k: int| 0 <= k < i as int ==> 
                output@[k] == (if exists|j: int| 0 <= j < k && names@[j] == names@[k] { "YES" } else { "NO" })
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j as int <= i as int,
                found == (exists|k: int| 0 <= k < j as int && names@[k] == names@[i as int])
            decreases i - j
        {
            if names[j] == names[i] {
                found = true;
            }
            j += 1;
        }
        if found {
            output.push("YES");
        } else {
            output.push("NO");
        }
    }
    output
}
// </vc-code>


}

fn main() {}