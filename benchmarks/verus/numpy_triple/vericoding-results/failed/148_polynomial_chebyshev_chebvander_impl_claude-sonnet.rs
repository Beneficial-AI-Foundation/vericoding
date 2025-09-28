// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proper preconditions to prevent arithmetic underflow */
fn chebyshev_t(n: usize, x: f32) -> (result: f32)
    requires n >= 0,
    ensures 
        n == 0 ==> result == 1.0f32,
        n == 1 ==> result == x,
    decreases n
{
    if n == 0 {
        1.0f32
    } else if n == 1 {
        x
    } else {
        2.0f32 * x * chebyshev_t((n - 1) as usize, x) - chebyshev_t((n - 2) as usize, x)
    }
}
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checks and overflow protection */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg + 1),
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i ==> result[j][1] == x@[j],
        decreases x.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        
        let mut k = 0;
        while k <= deg && k < usize::MAX
            invariant
                k <= deg + 1,
                k < usize::MAX,
                row.len() == k,
                k >= 1 ==> row[0] == 1.0f32,
                k >= 2 && deg >= 1 && i < x.len() ==> row[1] == x@[i as int],
            decreases deg + 1 - k
        {
            let val = if i < x.len() { chebyshev_t(k, x[i]) } else { 0.0f32 };
            row.push(val);
            k += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}