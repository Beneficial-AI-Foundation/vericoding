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
/* helper modified by LLM (iteration 5): removed unsupported as_bytes helper function, kept spec str_equal */
spec fn str_equal(s1: &str, s2: &str) -> bool {
    s1@ == s2@
}
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced as_bytes call with direct == for string comparison */
{
    let mut output = Vec::new();
    let mut seen = Vec::new();
    let mut idx: usize = 0;
    while idx < names.len()
        invariant
            idx >= 0,
            idx <= names.len(),
            output@.len() == idx,
            forall |i: int| 0 <= i < idx ==> 
                output@[i] == (if exists |j: int| 0 <= j < i && str_equal(names@[j], names@[i]) { "YES" } else { "NO" }),
        decreases names.len() - idx
    {
        let name = names[idx];
        let mut is_seen = false;
        let mut check_idx = 0;
        while check_idx < seen.len()
            invariant
                check_idx <= seen.len(),
                is_seen == exists |j: int| 0 <= j < check_idx as int && str_equal(seen@[j], name),
            decreases seen.len() - check_idx
        {
            if seen[check_idx] == name {
                is_seen = true;
            }
            check_idx += 1;
        }
        if is_seen {
            output.push("YES");
        } else {
            output.push("NO");
            seen.push(name);
        }
        idx += 1;
    }
    output
}
// </vc-code>


}

fn main() {}