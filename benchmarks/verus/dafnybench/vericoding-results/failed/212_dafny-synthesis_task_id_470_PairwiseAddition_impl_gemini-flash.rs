use vstd::prelude::*;

verus! {

// <vc-helpers>
fn int_div(a: int, b: int) -> (res: int)
    requires b != 0
    ensures res == a / b
{
    a / b
}
// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    let a_len = a.len();
    assert(a_len % 2 == 0);
    let a_len_div_2: usize = a_len / 2;

    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while (i < a_len_div_2)
        invariant
            i <= a_len_div_2,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == a[2 * j as int] + a[2 * j as int + 1],
    {
        let val1 = a[2 * i];
        let val2 = a[2 * i + 1];
        result.push(val1 + val2);
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {}

}