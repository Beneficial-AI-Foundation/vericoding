// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lagroots_lemma(c: Seq<i8>)
    requires
        c.len() == 2,
        c[1] != 0,
    ensures
        seq![1 + (c[0] as int / c[1] as int) as i8].len() == 1,
        seq![1 + (c[0] as int / c[1] as int) as i8][0] as int == 1 + c[0] as int / c[1] as int,
{
    assert(seq![1 + (c[0] as int / c[1] as int) as i8].len() == 1);
    assert(seq![1 + (c[0] as int / c[1] as int) as i8][0] as int == 1 + c[0] as int / c[1] as int);
}

/* helper modified by LLM (iteration 5): Fixed sequence indexing syntax using brackets instead of view method */
fn solve_linear(c0: i8, c1: i8) -> (root: i8)
    requires
        c1 != 0,
    ensures
        root as int == 1 + c0 as int / c1 as int,
{
    let result: i8 = (c0 / c1) + 1;
    result
}

// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i8>) -> (roots: Vec<i8>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] as int == 1 + c@[0] as int / c@[1] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence indexing syntax using brackets instead of view method */
    if c.len() == 2 {
        let c0 = c[0];
        let c1 = c[1];
        proof {
            lagroots_lemma(c@);
        }
        let root = solve_linear(c0, c1);
        let roots = vec![root];
        roots
    } else {
        let roots = Vec::new();
        roots
    }
}
// </vc-code>

}
fn main() {}