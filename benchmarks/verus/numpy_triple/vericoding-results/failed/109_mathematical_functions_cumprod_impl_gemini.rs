// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_product_prefix_recursive(a: Seq<int>, end: int)
    requires
        end > 0,
        end <= a.len(),
    ensures
        product_prefix(a, end) == product_prefix(a, end - 1) * a[end - 1],
{
    reveal_with_fuel(product_prefix, 2);
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
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result: Vec<i8> = Vec::new();
    result.push(a[0]);

    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            a.len() == n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == product_prefix(a@.map(|_idx, x: i8| x as int), j + 1),
        decreases n - i
    {
        proof {
            lemma_product_prefix_recursive(a@.map(|_idx, x: i8| x as int), (i + 1) as int);
        }

        let prev_val = result[i - 1];
        let current_a = a[i];
        let new_val = prev_val * current_a;
        result.push(new_val);

        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}