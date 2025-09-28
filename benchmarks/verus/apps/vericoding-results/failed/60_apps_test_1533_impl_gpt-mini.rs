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
/* helper modified by LLM (iteration 2): predicate for whether name at index i was seen before */
spec fn seen(names: Seq<&str>, i: int) -> bool {
    exists|j: int| 0 <= j < i && names[j] == names[i]
}
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize indices and cast to int in specs */
    let n = names.len();
    let mut output: Vec<&str> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            output.len() == i,
            forall|k: int| 0 <= k < i as int ==> output@[k] == (if exists|t: int| 0 <= t < k && names@[t] == names@[k] { "YES" } else { "NO" }),
        decreases n - i
    {
        let mut seen_flag: bool = false;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j as int <= i as int,
                output.len() == i,
                forall|k: int| 0 <= k < i as int ==> output@[k] == (if exists|t: int| 0 <= t < k && names@[t] == names@[k] { "YES" } else { "NO" }),
                seen_flag == (exists|t: int| 0 <= t < j as int && names@[t] == names@[i as int]),
            decreases i - j
        {
            if names.get(j) == names.get(i) {
                seen_flag = true;
                j = i;
            } else {
                j += 1;
            }
        }

        if seen_flag {
            output.push("YES");
        } else {
            output.push("NO");
        }

        proof {
            if seen_flag {
                assert(output.get(i) == Some("YES"));
            } else {
                assert(output.get(i) == Some("NO"));
            }
        }

        i += 1;
    }

    output
}
// </vc-code>


}

fn main() {}