use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    let mut i: usize = 0;
    let n = a.len();
    while i + 1 < n
        invariant
            i <= n,
            (i as int) % 2 == 0,
            result.len() == (i / 2) as usize,
            forall|j: int| 
                0 <= j < result.len() as int 
                ==> result@[j] == a@[2*j] + a@[2*j+1]
        decreases n - i
    {
        result.push(a[i] + a[i+1]);
        i += 2;
    }
    result
}
// </vc-code>

fn main() {}

}