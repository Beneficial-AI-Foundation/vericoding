// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing and type errors */
fn min_length_sublist_rec(s: Seq<Seq<int>>, i: nat) -> (min_sublist: Seq<int>)
    requires
        s.len() > 0,
        i < s.len(),
    ensures
        s.contains(min_sublist),
        forall |j: nat| i <= j < s.len() ==> min_sublist.len() <= s@[j as int].len(),
    decreases s.len() - i
{
    if i + 1 == s.len() {
        s@[i as int]
    } else {
        let rest_min = min_length_sublist_rec(s, i + 1);
        if s@[i as int].len() <= rest_min.len() {
            s@[i as int]
        } else {
            rest_min
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): calling helper with nat index */
    min_length_sublist_rec(s, 0)
}
// </vc-code>

}
fn main() {}