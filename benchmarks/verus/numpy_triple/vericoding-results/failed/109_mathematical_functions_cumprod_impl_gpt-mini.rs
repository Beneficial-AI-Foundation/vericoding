// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma for product_prefix(n+1) = product_prefix(n) * a[n] */
proof fn product_prefix_cons(a: Seq<int>, n: nat)
    ensures
        product_prefix(a, (n as int) + 1) == product_prefix(a, n as int) * a[n as int],
    decreases
        n
{
    if n == 0 {
        assert(product_prefix(a, 1) == a[0]);
        assert(product_prefix(a, 0) == 1);
        assert(product_prefix(a, (0 as int) + 1) == product_prefix(a, 0 as int) * a[0]);
    } else {
        product_prefix_cons(a, n - 1);
        assert(product_prefix(a, (n as int) + 1) == product_prefix(a, n as int) * a[n as int]);
    }
}
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
    /* code modified by LLM (iteration 5): implement cumprod without tracked vars, use lemma to maintain acc invariant */
    let mut result: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    let seq: Seq<int> = a@.map(|_i, x: i8| x as int);
    let mut acc: int = 1;
    while idx < a.len()
        invariant
            result.len() == idx,
            acc == product_prefix(seq, idx as int),
            forall|t: int| 0 <= t < idx as int ==> result[t as nat] as int == product_prefix(seq, t + 1),
        decreases
            a.len() - idx
    {
        acc = acc * (a[idx] as int);
        proof {
            product_prefix_cons(seq, idx as nat);
        }
        result.push(acc as i8);
        idx = idx + 1;
    }
    result
}
// </vc-code>


}
fn main() {}