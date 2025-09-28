// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermcompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c@.len() >= 2,
        c[c@.len() - 1] as int != 0,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    let m = c.len() - 1;
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            i <= m,
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k]@.len() == (m as int),
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                row@.len() == j as int,
            decreases m - j
        {
            row.push(0i8);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}