// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): transitivity of <= */
fn le_trans(a: int, b: int, c: int)
    requires
        a <= b,
        b <= c,
    ensures
        a <= c,
{
    proof {
        assert(a <= b);
        assert(b <= c);
        assert(a <= c);
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: &Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> #[trigger] sorted@[i] <= #[trigger] sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] s@[i] == #[trigger] sorted@[j],
        forall|x: i8| #[trigger] s@.contains(x) ==> #[trigger] sorted@.contains(x),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] sorted@[i] == #[trigger] s@[j],
        forall|x: i8| #[trigger] sorted@.contains(x) ==> #[trigger] s@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add loop decreases clauses and invariants */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    while i < s.len()
        invariant
            i <= s.len(),
        decreases
            s.len() - i
    {
        let x_ref = s.get(i).unwrap();
        let x = *x_ref;
        let mut j: usize = 0usize;
        while j < res.len() && *res.get(j).unwrap() <= x
            invariant
                j <= res.len(),
            decreases
                res.len() - j
        {
            j = j + 1usize;
        }
        res.insert(j, x);
        i = i + 1usize;
    }
    res
}
// </vc-code>


}

fn main() {}