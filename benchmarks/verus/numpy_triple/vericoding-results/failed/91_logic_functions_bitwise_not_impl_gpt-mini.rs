// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves that -(x + 1) fits in i8 range */
fn lemma_neg_add_one_fits(x: i8)
    ensures
        -(x as int + 1) >= -128,
        -(x as int + 1) <= 127,
{
    proof {
        let xi: int = x as int;
        assert(xi >= -128);
        assert(xi <= 127);
        assert(xi + 1 <= 128);
        assert(xi + 1 >= -127);
        assert(-(xi + 1) >= -128);
        assert(-(xi + 1) <= 127);
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with usize indices, compute tmp as i16, prove range, cast to i8 and push */
    let n: usize = x.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            res.view().len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> res.view()@[j] as int == -(x.view()@[j] as int + 1),
        decreases n - i
    {
        let xi: i8 = x[i];
        let tmp: i16 = -((xi as i16) + 1);
        proof {
            let tmp_int: int = tmp as int;
            lemma_neg_add_one_fits(xi);
            assert(tmp_int == -(xi as int + 1));
            assert(tmp_int >= -128);
            assert(tmp_int <= 127);
        }
        let t: i8 = tmp as i8;
        res.push(t);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}