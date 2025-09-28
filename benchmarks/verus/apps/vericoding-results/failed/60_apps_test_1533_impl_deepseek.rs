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

spec fn seen_before(names: Seq<&str>, name: &str, idx: int) -> bool 
    decreases idx
{
    exists|j: int| 0 <= j < idx && names[j] == name
}

proof fn valid_output_lemma(names: Seq<&str>, output: Seq<&str>, i: int) 
    requires
        output.len() == names.len(),
        forall|k: int| 0 <= k < names.len() ==> output[k] == (if seen_before(names, names[k], k) { "YES" } else { "NO" }),
        0 <= i < names.len()
    ensures
        output[i] == (if exists|j: int| 0 <= j < i && names[j] == names[i] { "YES" } else { "NO" })
{}

/* helper modified by LLM (iteration 5): fixed type conversion in seen_before calls */
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversion in seen_before calls */
    let mut output: Vec<&str> = Vec::new();
    let mut seen: Vec<&str> = Vec::new();
    
    let size = names.len();
    let mut i = 0;
    while i < size
        invariant
            output.len() == i,
            seen.len() == i,
            forall|k: int| 0 <= k < i ==> output[k] == (if seen_before(names@, names[k], k) { "YES" } else { "NO" })
    {
        let name = names[i];
        let mut j = 0;
        let mut found = false;
        while j < i
            invariant
                j >= 0,
                j <= i,
                found == seen_before(names@, names[i], j as int)
        {
            if seen[j] == name {
                found = true;
                break;
            }
            j += 1;
        }
        
        if found {
            output.push("YES");
        } else {
            output.push("NO");
        }
        seen.push(name);
        i += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}