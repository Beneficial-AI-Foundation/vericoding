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
fn already_seen(names: &Vec<&str>, i: int) -> (seen: bool)
    requires
        0 <= i < names.len(),
    ensures
        seen == (exists|j: int| 0 <= j < i && names@[j] == names@[i]),
{
    let target = names[i as usize];
    let mut j: usize = 0;
    while j < i as usize
        invariant
            0 <= j <= i as usize,
            forall|k: int| 0 <= k < j as int ==> names@[k] != target,
        decreases (i as usize) - j
    {
        if names[j] == target {
            return true;
        }
        j = j + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn solve(names: Vec<&str>) -> (output: Vec<&str>)
    ensures valid_output(names@, output@)
// </vc-spec>
// <vc-code>
{
    let mut output: Vec<&str> = Vec::new();
    let mut i: usize = 0;
    while i < names.len()
        invariant
            0 <= i <= names.len(),
            output.len() == i,
            forall|k: int| 0 <= k < i ==> 
                output@[k] == (if exists|j: int| 0 <= j < k && names@[j] == names@[k] { "YES" } else { "NO" }),
        decreases names.len() - i
    {
        let seen = already_seen(names, i as int);
        if seen {
            output.push("YES");
        } else {
            output.push("NO");
        }
        i = i + 1;
    }
    return output;
}
// </vc-code>


}

fn main() {}