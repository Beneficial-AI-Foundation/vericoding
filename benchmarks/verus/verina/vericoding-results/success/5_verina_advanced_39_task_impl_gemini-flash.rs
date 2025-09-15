// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Retaining previous helper. */
fn max(a:usize,b:usize) -> usize { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous compilation error was due to malformed invariants (missing `sn_` for `snapshot_` for sequence type `lst`). The `lst` variable is of type `&Vec<usize>`, so we need to dereference it when accessing its components using `lst@[k]` as `lst` is already of `Seq` in specification. Also, the first invariant was `0 <= i && i <= lst.len()`. As noted by the compiler, invariants need a `bool` expression. So each individual invariant must be a `bool` expression by itself. For example, `0 <= i`, `i <= lst.len()`. */
{
    let mut max_val: usize = lst[0];
    let mut i: usize = 1;

    while i < lst.len()
        invariant 
            0 <= i,
            i <= lst.len(),
            exists|k: int| 0 <= k < i && lst@[k] == max_val,
            forall|k: int| 0 <= k < i ==> lst@[k] <= max_val
        decreases lst.len() - i
    {
        if lst[i] > max_val {
            max_val = lst[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}