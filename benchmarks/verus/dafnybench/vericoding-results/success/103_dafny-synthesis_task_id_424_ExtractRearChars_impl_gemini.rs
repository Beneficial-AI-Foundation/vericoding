// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn extract_rear_chars(l: &Vec<Vec<char>>) -> (r: Vec<char>)
    requires forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    ensures 
        r.len() == l.len()
        && forall|i: int| 0 <= i < l.len() ==> r[i] == l[i][l[i].len() - 1]
// </vc-spec>
// <vc-code>
{
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            r.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == l@[j]@[l@[j].len() - 1],
            forall|k: int| 0 <= k < l.len() ==> l@[k].len() > 0,
        decreases l.len() - i
    {
        let last_char = l[i][l[i].len() - 1];
        r.push(last_char);
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}