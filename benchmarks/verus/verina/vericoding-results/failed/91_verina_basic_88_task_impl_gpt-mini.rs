// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma that sequence length is non-negative */
proof fn seq_len_nonneg<T>(s: &Seq<T>)
    ensures
        s.len() >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): convert Seq to Vec with nat-index loop */
    let mut v: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < xs.len()
        invariant
            v.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> v@[j] == xs[j],
        decreases xs.len() - i
    {
        let elem: i32 = xs[i as int];
        v.push(elem);
        i = i + 1;
    }
    proof {
        assert(v.len() == xs.len());
        assert(forall|j: int| 0 <= j && j < xs.len() ==> v@[j] == xs[j]);
    }
    v
}

// </vc-code>

}
fn main() {}