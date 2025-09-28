use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn add_rows_spec(row_a: Seq<int>, row_b: Seq<int>) -> Seq<int>
    recommends row_a.len() == row_b.len()
{
    Seq::new(row_a.len(), |j: int| row_a[j] + row_b[j])
}

fn add_rows(row_a: Seq<int>, row_b: Seq<int>) -> (result: Seq<int>)
    requires row_a.len() == row_b.len()
    ensures 
        result.len() == row_a.len(),
        forall|j: int| 0 <= j < result.len() ==> result[j] == row_a[j] + row_b[j]
{
    let mut result = Seq::<int>::empty();
    let mut j: usize = 0;
    
    while j < row_a.len()
        invariant
            0 <= j <= row_a.len(),
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result[k] == row_a[k] + row_b[k]
    {
        result = result.push(row_a[j] + row_b[j]);
        j += 1;
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
    let mut result = Seq::<Seq<int>>::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == a[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==> 
                result[k][j] == a[k][j] + b[k][j]
    {
        let row_sum = add_rows(a@[i], b@[i]);
        result = result.push(row_sum);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}