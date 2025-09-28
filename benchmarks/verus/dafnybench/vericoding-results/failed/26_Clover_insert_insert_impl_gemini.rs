// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert(line: &mut Vec<char>, l: int, nl: &Vec<char>, p: int, at: int)
    requires 
        0 <= l + p <= old(line).len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
    ensures 
        forall|i: int| (0 <= i < p) ==> line[at + i] == nl[i],
        forall|i: int| (0 <= i < at) ==> line[i] == old(line)[i],
        forall|i: int| (at + p <= i < l + p) ==> line[i] == old(line)[i - p],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed non-primitive casts from int to usize */
{
    let ghost old_line = line@;

    let at_u = at as nat as usize;
    let l_u = l as nat as usize;
    let p_u = p as nat as usize;

    let mut i = l_u;
    while i > at_u
        invariant
            line.len() == old_line.len(),
            at_u <= i <= l_u,
            p >= 0,
            forall|k: int| 0 <= k < at ==> line@[k] == old_line@[k],
            forall|k: int| at <= k < i as int ==> line@[k] == old_line@[k],
            forall|k: int| i as int <= k < l ==> line@[(k + p) as nat] == old_line@[k as nat],
        decreases i
    {
        i = i - 1;
        let val = line[i];
        line[i + p_u] = val;
    }

    let mut j: usize = 0;
    while j < p_u
        invariant
            0 <= j <= p_u,
            line.len() == old_line.len(),
            p >= 0,
            forall|k: int| 0 <= k < at ==> line@[k] == old_line@[k],
            forall|k: int| at <= k < l ==> line@[(k + p) as nat] == old_line@[k as nat],
            forall|k: int| 0 <= k < j as int ==> line@[(at + k) as nat] == nl@[k as nat],
        decreases p_u - j
    {
        let val = nl[j];
        line[at_u + j] = val;
        j = j + 1;
    }
}
// </vc-code>

}
fn main() {}