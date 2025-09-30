// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn delete(line: &mut Vec<char>, l: usize, at: usize, p: usize)
    requires
        l <= old(line).len(),
        at + p <= l,
    ensures
        line@ == old(line)@.subrange(0, at as int) + old(line)@.subrange((at + p) as int, l as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): switched loop invariants from subrange-based properties to equivalent forall quantifiers to aid the SMT prover */
    let mut i = at;
    while i < l - p
        invariant
            at <= i,
            i <= l - p,
            l <= old(line).len(),
            at + p <= l,
            line.len() == old(line).len(),
            line@.subrange(0, at as int) == old(line)@.subrange(0, at as int),
            forall|j: int| at <= j < i ==> line@[j] == old(line)@[j + p],
            forall|j: int| i <= j < line.len() ==> line@[j] == old(line)@[j],
        decreases l - p - i
    {
        line[i] = line[i + p];
        i = i + 1;
    }
    line.truncate(l - p);
}
// </vc-code>

}
fn main() {}