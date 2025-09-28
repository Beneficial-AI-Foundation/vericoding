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
spec fn has_duplicate_before(names: Seq<&str>, i: int) -> bool {
    exists|j: int| 0 <= j < i && names[j] == names[i]
}

/* helper modified by LLM (iteration 5): fixed lemma syntax by adding proof block */
proof fn valid_output_step(names: Seq<&str>, output: Seq<&str>, i: int)
    requires
        0 <= i < names.len(),
        output.len() == names.len(),
        forall|k: int| 0 <= k < i ==> output[k] == (if has_duplicate_before(names, k) { "YES" } else { "NO" }),
        output[i] == (if has_duplicate_before(names, i) { "YES" } else { "NO" })
    ensures
        forall|k: int| 0 <= k <= i ==> output[k] == (if has_duplicate_before(names, k) { "YES" } else { "NO" })
{
}

proof fn has_duplicate_equiv(names: Seq<&str>, i: int)
    requires 0 <= i < names.len()
    ensures has_duplicate_before(names, i) == (exists|j: int| 0 <= j < i && names[j] == names[i])
{
}
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed lemma invocation syntax */
    let mut output: Vec<&str> = Vec::new();
    let mut idx = 0;
    
    while idx < names.len()
        invariant
            0 <= idx <= names.len(),
            output.len() == idx,
            forall|i: int| 0 <= i < idx ==> 
                output@[i] == (if exists|j: int| 0 <= j < i && names@[j] == names@[i] { "YES" } else { "NO" })
    {
        let mut found = false;
        let mut j = 0;
        
        while j < idx
            invariant
                0 <= j <= idx,
                found == (exists|k: int| 0 <= k < j && names@[k] == names@[idx])
        {
            if names[j] == names[idx] {
                found = true;
            }
            j += 1;
        }
        
        if found {
            output.push("YES");
        } else {
            output.push("NO");
        }
        
        proof {
            has_duplicate_equiv(names@, idx as int);
        }
        
        idx += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}