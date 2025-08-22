use vstd::prelude::*;

verus! {

        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if s[i] == old { new } else { s[i] }),
{
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (if s[j] == old { new } else { s[j] }),
    {
        result.push(if s[i] == old { new } else { s[i] });
        i = i + 1;
    }
    result
}

fn main() {}
}