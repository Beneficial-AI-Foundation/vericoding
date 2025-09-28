// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate bitwise_or_int spec to bitwise OR */
proof fn bitwise_or_int_spec(x: i32, y: i32)
    ensures
        bitwise_or_int(x, y) == x | y,
{
    assert(bitwise_or_int(x, y) == x | y);
}

/* helper modified by LLM (iteration 5): unfold vector-level spec into elementwise OR spec */
proof fn bitwise_or_vec_spec(x: Seq<i32>, y: Seq<i32>)
    requires x.len() == y.len(),
    ensures
        bitwise_or_vec(x, y) == Seq::new(x.len(), |i: int| bitwise_or_int(x[i], y[i])),
{
    // Relate the elementwise spec to the sequence-level spec
    // First show sequence of bitwise_or_int equals sequence of concrete ORs
    assert(Seq::new(x.len(), |i: int| bitwise_or_int(x[i], y[i])) == Seq::new(x.len(), |i: int| x[i] | y[i]));
    // Then relate the spec-level bitwise_or_vec to the concrete OR sequence
    assert(bitwise_or_vec(x, y) == Seq::new(x.len(), |i: int| x[i] | y[i]));
    // Conclude the desired equality
    assert(bitwise_or_vec(x, y) == Seq::new(x.len(), |i: int| bitwise_or_int(x[i], y[i])));
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
/* code modified by LLM (iteration 5): implement elementwise OR and prove relation to spec */
{
    let n: usize = x1.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            result@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == bitwise_or_int(x1@[j], x2@[j]),
        decreases (n as int) - (i as int)
    {
        // establish safe indexing
        assert(i < x1.len());
        assert(i < x2.len());
        let a: i32 = x1[i];
        let b: i32 = x2[i];
        let v: i32 = a | b;
        result.push(v);
        i += 1;
    }
    proof {
        bitwise_or_vec_spec(x1@, x2@);
        assert(result@ == bitwise_or_vec(x1@, x2@));
    }
    result
}

// </vc-code>

}
fn main() {}