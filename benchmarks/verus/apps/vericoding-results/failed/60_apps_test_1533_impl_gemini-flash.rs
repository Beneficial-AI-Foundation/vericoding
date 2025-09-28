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
/* helper modified by LLM (iteration 5): The previous iteration removed the helper section, but Verus requires a placeholder even if empty. This iteration re-adds the empty helper section. */
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous error was due to indexing `Seq<&str>` using `@` notation. Removed `@` when indexing. */
{
    let mut output: Vec<&'static str> = Vec::new();
    let mut i: usize = 0;

    while i < names.len()
        invariant 
            0 <= i as int,
            i <= names.len(),
            output.len() == i,
            forall|idx: int| 0 <= idx < i as int ==> 
                output@[idx] == (if exists|k: int| 0 <= k < idx && names@[k] == names@[idx] { "YES" } else { "NO" })
        decreases names.len() - i
    {
        let mut found_duplicate: bool = false;
        let mut j: usize = 0;

        while j < i
            invariant
                0 <= j as int,
                j <= i,
                forall |k: int| 0 <= k < j as int ==> (found_duplicate || names[k as usize] != names[i as usize]),
                found_duplicate ==> (exists|k: int| 0 <= k < j as int && names[k as usize] == names[i as usize])
            decreases i - j
        {
            if names[j] == names[i] {
                found_duplicate = true;
            }
            j = j + 1;
        }

        if found_duplicate {
            output.push("YES");
        } else {
            output.push("NO");
        }
        
        i = i + 1;
    }

    output
}
// </vc-code>


}

fn main() {}