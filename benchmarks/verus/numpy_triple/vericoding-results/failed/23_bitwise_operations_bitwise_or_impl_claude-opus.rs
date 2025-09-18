// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed verus_bitwise_or to spec function */
spec fn verus_bitwise_or(a: i32, b: i32) -> i32 {
    bitwise_or_int(a, b)
}

proof fn lemma_bitwise_or_properties(x: i32, y: i32)
    ensures
        y == 0 ==> (x | y) == x,
        x == 0 ==> (x | y) == y,
        (x == -1i32 || y == -1i32) ==> (x | y) == -1i32
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
    /* code modified by LLM (iteration 5): added decreases clause to loop */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i as int ==> result[j] == bitwise_or_int(x1[j], x2[j]),
            forall|j: int| 0 <= j < i as int && x2[j] == 0 ==> result[j] == x1[j],
            forall|j: int| 0 <= j < i as int && x1[j] == 0 ==> result[j] == x2[j],
            forall|j: int| 0 <= j < i as int && (x1[j] == -1i32 || x2[j] == -1i32) ==> result[j] == -1i32
        decreases n - i
    {
        let val = x1[i] | x2[i];
        proof {
            lemma_bitwise_or_properties(x1[i as int], x2[i as int]);
        }
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}