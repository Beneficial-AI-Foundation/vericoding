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
/* helper modified by LLM (iteration 5): trivial &str equality wrapper used in exec code */
fn eq_str(a: &str, b: &str) -> (res: bool)
    ensures
        res == (a == b),
{
    a == b
}

// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): verified scan using curr element, avoiding problematic proof asserts */
    let mut output: Vec<&str> = Vec::new();
    let mut i: usize = 0;
    while i < names.len()
        invariant
            0 <= i as int <= names@.len(),
            output.len() as int == i as int,
            forall|k: int|
                0 <= k < i as int ==> output@[k] == (if exists|j: int| 0 <= j < k && names@[j] == names@[k] { "YES" } else { "NO" }),
        decreases names@.len() - i as int
    {
        let curr = names[i];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j as int <= i as int,
                0 <= i as int <= names@.len(),
                found == (exists|m: int| 0 <= m < j as int && names@[m] == curr),
            decreases i as int - j as int
        {
            if eq_str(names[j], curr) {
                found = true;
                j = i; // break
            } else {
                j += 1;
            }
        }
        if found { output.push("YES"); } else { output.push("NO"); }
        i += 1;
    }
    output
}
// </vc-code>


}

fn main() {}