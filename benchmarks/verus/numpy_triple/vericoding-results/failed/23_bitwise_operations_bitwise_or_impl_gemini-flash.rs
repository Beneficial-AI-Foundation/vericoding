// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate definition of `bitwise_or_int` to fix compilation error. */
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < x1.len()
        invariant
            result.len() == i,
            result.len() <= x1.len(),
            forall|j: int| 0 <= j < i as int ==> result.view()[j] == (x1.view()[j] | x2.view()[j])
        decreases x1.len() - i
    {
        let val: i32 = x1[i] | x2[i];
        result.push(val);
        i = i + 1;
    }
    proof {
        assert(result@ == Seq::new(x1.len() as int, |k: int| bitwise_or_int(x1@[k], x2@[k])));
        assert(result@ == bitwise_or_vec(x1@, x2@));
        // The following asserts are needed to satisfy the additional postconditions
        assert(forall|k: int| 0 <= k < result.len() && x2@[k] == 0 ==> result@[k] == (x1@[k] | x2@[k]));
        assert(forall|k: int| 0 <= k < result.len() && x1@[k] == 0 ==> result@[k] == (x1@[k] | x2@[k]));
        assert(forall|k: int| 0 <= k < result.len() && (x1@[k] == -1i32 || x2@[k] == -1i32) ==> result@[k] == (x1@[k] | x2@[k]));
    }
    result
}
// </vc-code>

}
fn main() {}