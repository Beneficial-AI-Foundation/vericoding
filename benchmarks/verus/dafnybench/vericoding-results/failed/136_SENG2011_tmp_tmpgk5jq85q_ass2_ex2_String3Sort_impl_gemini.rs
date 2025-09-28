// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
spec fn min(a: char, b: char) -> char { if a <= b { a } else { b } }

spec fn max(a: char, b: char) -> char { if a <= b { b } else { a } }

/* helper modified by LLM (iteration 2): implemented empty proof body, which Verus can solve automatically */
proof fn lemma_max_of_min(a: char, b: char, c: char)
    requires
        a <= b,
    ensures
        max(a, min(b, c)) <= max(b, c),
{
}

/* helper modified by LLM (iteration 3): fixed compilation error by naming the return value in the signature */
fn order(c1: char, c2: char) -> (ret: (char, char))
    ensures
        ret.0 == min(c1, c2),
        ret.1 == max(c1, c2),
        ret.0 <= ret.1,
        seq![ret.0, ret.1].to_multiset() == seq![c1, c2].to_multiset(),
{
    if c1 <= c2 {
        (c1, c2)
    } else {
        (c2, c1)
    }
}
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error using .index() for exec-code sequence access */
    let c0 = a.index(0);
    let c1 = a.index(1);
    let c2 = a.index(2);

    let (t0, t1) = order(c0, c1);
    let (u1, u2) = order(t1, c2);
    let (v0, v1) = order(t0, u1);

    let b = seq![v0, v1, u2];

    proof {
        lemma_max_of_min(t0, t1, c2);
    }

    b
}
// </vc-code>

}
fn main() {}