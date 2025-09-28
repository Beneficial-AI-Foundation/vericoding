// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn product_prefix(a: Seq<int>, end: int) -> int
    decreases end
{
    if end <= 0 {
        1
    } else if end == 1 {
        a[0]
    } else {
        product_prefix(a, end - 1) * a[end - 1]
    }
}

fn cumprod(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == product_prefix(a@.map(|_index, x: i8| x as int), i + 1),
        forall|i: int, j: int| 0 <= i < a.len() && j == i + 1 && j < a.len() ==> 
            result[j] as int == (result[i] as int) * (a[j] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed compilation errors by casting indices to int for spec functions */
    let mut result = Vec::new();
    let mut exec_prod: i64 = 1;
    let ghost mut prod: int = 1;
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            prod == product_prefix(a@.map(|_index, x: i8| x as int), i as int)
        decreases a.len() - i
    {
        let elem_i64 = a[i] as i64;
        let ghost elem: int = a@[i as int] as int;
        proof {
            prod = prod * elem;
        }
        exec_prod = exec_prod * elem_i64;
        result.push(exec_prod as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}