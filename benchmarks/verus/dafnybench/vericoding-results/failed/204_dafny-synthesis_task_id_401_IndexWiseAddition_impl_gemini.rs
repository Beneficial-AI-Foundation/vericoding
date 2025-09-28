// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Switched loop counter to int and used correct Seq indexing. */
fn add_rows(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
{
    let mut result = Seq::empty();
    let mut i: int = 0;
    while i < a.len() as int
        invariant
            a.len() == b.len(),
            0 <= i <= a.len() as int,
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] + b[j],
        decreases (a.len() as int) - i
    {
        result = result.push(a[i] + b[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn index_wise_addition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires 
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i][j] + b[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Switched loop counter to int and used correct Seq indexing. */
    let mut result: Seq<Seq<int>> = Seq::empty();
    let mut i: int = 0;
    while i < a.len() as int
        invariant
            a.len() == b.len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == b[k].len(),
            0 <= i <= a.len() as int,
            result.len() == i as nat,
            forall|k: int| 0 <= k < i ==> result[k].len() == a[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==> 
                result[k][j] == a[k][j] + b[k][j],
        decreases (a.len() as int) - i
    {
        let new_row = add_rows(a[i], b[i]);
        result = result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}