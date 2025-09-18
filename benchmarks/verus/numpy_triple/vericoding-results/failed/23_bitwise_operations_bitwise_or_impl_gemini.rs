// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes were necessary. The lemma is correct. */
proof fn lemma_bitwise_or_properties(x: i32, y: i32)
    ensures
        (y == 0) ==> ((x | y) == x),
        (x == 0) ==> ((x | y) == y),
        (x == -1i32 || y == -1i32) ==> ((x | y) == -1i32),
{
    if y == 0 {
        assert((x | y) == x) by(bit_vector);
    }
    if x == 0 {
        assert((x | y) == y) by(bit_vector);
    }
    if x == -1i32 {
        assert((x | y) == -1i32) by(bit_vector);
    }
    if y == -1i32 {
        assert((x | y) == -1i32) by(bit_vector);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn bitwise_or_int(x: i32, y: i32) -> i32 {
    x
}

spec fn bitwise_and_int(x: i32, y: i32) -> i32 {
    x
}

spec fn bitwise_or_vec(x: Seq<i32>, y: Seq<i32>) -> Seq<i32>
    recommends x.len() == y.len()
{
    Seq::new(x.len(), |i: int| x[i])
}

fn bitwise_or_fn(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == bitwise_or_int(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && (x1[i] == -1i32 || x2[i] == -1i32) ==> result[i] == -1i32,
        result@ == bitwise_or_vec(x1@, x2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected indexing in proof block to fix compilation error. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == bitwise_or_int(x1[j], x2[j]),
            forall|j: int| 0 <= j < i && x2[j] == 0 ==> result[j] == x1[j],
            forall|j: int| 0 <= j < i && x1[j] == 0 ==> result[j] == x2[j],
            forall|j: int| 0 <= j < i && (x1[j] == -1i32 || x2[j] == -1i32) ==> result[j] == -1i32,
            result@ == bitwise_or_vec(x1@.subrange(0, i as int), x2@.subrange(0, i as int)),
    {
        let val = x1[i] | x2[i];
        proof {
            lemma_bitwise_or_properties(x1@[i as int], x2@[i as int]);
        }
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}