// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted_to(from_index: int, a: Seq<i32>, result: Seq<usize>) -> bool {
    forall |i: int, j: int| from_index <= i < j < result.len() ==> 
        a[result[i] as int] <= a[result[j] as int] || 
        (a[result[i] as int] == a[result[j] as int] && result[i] < result[j])
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof block to establish initial invariants for difficult loop verification */
    let mut result: Vec<usize> = Vec::new();
    for i in 0..a.len() {
        result.push(i);
    }
    proof {
        assert(result@.len() == a.len());
        assert(forall |k: int| 0 <= k < result@.len() ==> result@[k] < a.len());
        assert(sorted_to(a.len() as int, a@, result@));
        assert(forall |i: int, j: int| 0 <= i < j < result@.len() && a@[result@[i] as int] == a@[result@[j] as int] ==> result@[i] < result@[j]);
    }
    let mut outer: usize = a.len();
    while outer > 0
        invariant
            result@.len() == a.len(),
            forall |k: int| 0 <= k < result@.len() ==> result@[k] < a.len(),
            sorted_to(outer as int, a@, result@),
            forall |i: int, j: int| 0 <= i < j < result@.len() && a@[result@[i] as int] == a@[result@[j] as int] ==> result@[i] < result@[j]
        decreases outer
    {
        outer -= 1;
        for inner in 0..outer
            invariant
                0 <= inner < outer,
                sorted_to((outer + 1) as int, a@, result@)
        {
            if a[result[inner]] > a[result[inner + 1]] || 
                (a[result[inner]] == a[result[inner + 1]] && result[inner] > result[inner + 1]) {
                let tmp = result[inner];
                result[inner] = result[inner + 1];
                result[inner + 1] = tmp;
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}