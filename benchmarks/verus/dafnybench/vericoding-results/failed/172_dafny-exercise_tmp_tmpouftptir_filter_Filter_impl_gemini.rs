// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected order of ensures and decreases clauses */
fn filter_recursive(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures
        forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
    decreases a.len()
{
    if a.len() == 0 {
        Set::empty()
    } else {
        let first = a[0];
        let rest = a.subrange(1, a.len() as int);
        let filtered_rest = filter_recursive(rest, b);
        if b.contains(first) {
            filtered_rest.insert(first)
        } else {
            filtered_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation relies on the recursive helper */
    filter_recursive(a, b)
}
// </vc-code>

}
fn main() {}