// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn build_row(xi: f32, deg: usize) -> (row: Vec<f32>)
    ensures
        row.len() == deg + 1,
        row[0] == 1.0f32,
        deg >= 1 ==> row[1] == xi
{
    let mut row: Vec<f32> = Vec::new();
    row.push(1.0f32);
    if deg >= 1 {
        row.push(xi);
    }
    let target = deg + 1;
    while row.len() < target
        invariant row.len() <= target
        invariant row.len() >= if deg >= 1 { 2 } else { 1 }
        decreases (target as int) - (row.len() as int)
    {
        row.push(0.0f32);
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant result.len() == i
        invariant forall|j: int| 0 <= j < i as int ==> result[j].len() == deg + 1
        invariant forall|j: int| 0 <= j < i as int ==> result[j][0] == 1.0f32
        invariant deg >= 1 ==> forall|j: int| 0 <= j < i as int ==> result[j][1] == x[j]
        decreases (n as int) - (i as int)
    {
        let xi = x[i];
        let row = build_row(xi, deg);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}