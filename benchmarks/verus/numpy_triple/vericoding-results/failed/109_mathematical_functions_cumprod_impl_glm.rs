// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn cumprod_helper(a: Seq<int>, index: int, acc: int) -> int
    requires
        0 <= index <= a.len(),
    decreases
        a.len() - index
{
    if index == a.len() {
        acc
    } else {
        cumprod_helper(a, index + 1, acc * a[index])
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
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    let n = a.len();
    let mut acc = 1;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            acc == product_prefix(a@.map(|_index, x: i8| x as int), i),
            forall|j: int| 0 <= j < i ==> result[j] as int == product_prefix(a@.map(|_index, x: i8| x as int), j + 1),
        decreases
            n - i
    {
        if i > 0 {
            acc = acc * (a[i] as int);
        } else {
            acc = a[0] as int;
        }
        result.push(acc as i8);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}