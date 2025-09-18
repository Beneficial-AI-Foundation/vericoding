// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed uninterp and fixed bitwise_or_int_spec definition */
spec fn bitwise_or_int_spec(x: i32, y: i32) -> i32 {
    x | y
}

proof fn bitwise_or_properties(x: i32, y: i32)
    ensures
        y == 0 ==> bitwise_or_int_spec(x, y) == x,
        x == 0 ==> bitwise_or_int_spec(x, y) == y,
        (x == -1i32 || y == -1i32) ==> bitwise_or_int_spec(x, y) == -1i32
{
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
    /* code modified by LLM (iteration 5): fixed type mismatches by using @ for vector indexing in specs */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == bitwise_or_int(x1@[j], x2@[j]),
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result[j] == x2@[j],
            forall|j: int| 0 <= j < i && (x1@[j] == -1i32 || x2@[j] == -1i32) ==> result[j] == -1i32
        decreases x1.len() - i
    {
        let or_result = x1[i] | x2[i];
        proof {
            assert(or_result == bitwise_or_int(x1@[i as int], x2@[i as int]));
            if x2@[i as int] == 0 {
                assert(or_result == x1@[i as int]);
            }
            if x1@[i as int] == 0 {
                assert(or_result == x2@[i as int]);
            }
            if x1@[i as int] == -1i32 || x2@[i as int] == -1i32 {
                assert(or_result == -1i32);
            }
        }
        result.push(or_result);
        i += 1;
    }
    proof {
        assert(result@ == bitwise_or_vec(x1@, x2@));
    }
    result
}
// </vc-code>

}
fn main() {}