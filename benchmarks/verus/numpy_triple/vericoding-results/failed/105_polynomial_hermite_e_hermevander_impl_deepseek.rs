// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix f64 type handling and usize/int conversions */
proof fn hermevander_spec_lemma_0(x: Seq<f64>, deg: nat, result: Seq<Seq<f64>>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i]
{
}

proof fn two_dim_vec_len_lemma<T>(v: Vec<Vec<T>>, i: int)
    requires
        0 <= i < v.len()
    ensures
        v@[i].len() == v[i].len()
{
}

proof fn two_dim_vec_index_lemma<T>(v: Vec<Vec<T>>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v[i].len()
    ensures
        v@[i][j] == v[i][j]
{
}

fn create_zero_vector(len: usize) -> (v: Vec<f64>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < len ==> v[i] == 0.0
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == 0.0
    {
        v.push(0.0);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix f64 type handling and remove unnecessary casts */
{
    let len = x.len();
    let mut result = Vec::with_capacity(len);
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let row: &Vec<f64> = &result[j];
                row.len() == deg + 1 &&
                row[0] == 1.0 &&
                (deg > 0 ==> row[1] == x[i])
            }
    {
        let mut row = create_zero_vector(deg + 1);
        row[0] = 1.0;
        
        if deg > 0 {
            row[1] = x[i];
            
            let mut k: usize = 2;
            while k <= deg
                invariant
                    2 <= k <= deg + 1,
                    row.len() == deg + 1,
                    row[0] == 1.0,
                    row[1] == x[i],
                    forall|j: int| k <= j <= deg ==> row[j] == 0.0
            {
                if k < deg + 1 {
                    row[k] = 0.0;
                }
                k += 1;
            }
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}