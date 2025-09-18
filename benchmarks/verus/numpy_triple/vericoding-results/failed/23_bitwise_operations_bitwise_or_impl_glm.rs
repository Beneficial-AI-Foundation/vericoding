// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to prove properties of bitwise OR */
proof fn lemma_bitwise_or_properties(x: i32, y: i32)
    ensures
        x == 0 ==> (x | y) == y,
        y == 0 ==> (x | y) == x,
        x == -1 || y == -1 ==> (x | y) == -1,
{
    assert(x == 0 ==> (x | y) == y);
    assert(y == 0 ==> (x | y) == x);
    assert(x == -1 || y == -1 ==> (x | y) == -1);
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
    /* code modified by LLM (iteration 5): fixed index type in proof block by converting to int */
    let mut result = Vec::new();
    for i in 0..x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] | x2@[j],
    {
        result.push(x1[i] | x2[i]);
    }
    proof {
        for i in 0..result.len() as int {
            lemma_bitwise_or_properties(x1@[i], x2@[i]);
            if x1@[i] == 0 {
                assert(result@[i] == x2@[i]);
            }
            if x1@[i] == -1 || x2@[i] == -1 {
                assert(result@[i] == -1);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}