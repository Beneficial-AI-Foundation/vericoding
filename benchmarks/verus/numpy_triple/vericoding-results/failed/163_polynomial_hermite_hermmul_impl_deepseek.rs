// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

predicate is_zero_vec(v: Vec<i8>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] == 0
}

fn zero_vec(len: nat) -> (v: Vec<i8>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < len ==> v[i] == 0,
{
    let mut v = Vec::new();
    let mut i: nat = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == 0,
        decreases len - i,
    {
        v.push(0);
        i = i + 1;
    }
    v
}

// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c1[i] as int * c2[0] as int,
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] as int == c2[i] as int * c1[0] as int,

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error in predicate usage */
    if c1.len() == 0 || c2.len() == 0 {
        let mut result = Vec::new();
        result.push(0);
        result
    } else if is_zero_vec(c1) || is_zero_vec(c2) {
        zero_vec(c1.len() + c2.len() - 1)
    } else if c2.len() == 1 {
        let mut result = Vec::with_capacity(c1.len());
        let mut i = 0;
        while i < c1.len()
            invariant
                0 <= i <= c1.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result[k] == (c1[k] as int * c2[0] as int) as i8,
            decreases c1.len() - i,
        {
            result.push((c1[i] as i32 * c2[0] as i32) as i8);
            i = i + 1;
        }
        result
    } else if c1.len() == 1 {
        let mut result = Vec::with_capacity(c2.len());
        let mut i = 0;
        while i < c2.len()
            invariant
                0 <= i <= c2.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result[k] == (c2[k] as int * c1[0] as int) as i8,
            decreases c2.len() - i,
        {
            result.push((c2[i] as i32 * c1[0] as i32) as i8);
            i = i + 1;
        }
        result
    } else {
        let n = c1.len() + c2.len() - 1;
        let mut result = zero_vec(n);
        
        let mut i: nat = 0;
        while i < c1.len()
            invariant
                0 <= i <= c1.len(),
                result.len() == n,
                forall|p: int, q: int| 0 <= p < i && 0 <= q < c2.len() ==> 
                    result[p + q] == (c1[p] as int * c2[q] as int) as i8,
            decreases c1.len() - i,
        {
            let mut j: nat = 0;
            while j < c2.len()
                invariant
                    0 <= j <= c2.len(),
                    result.len() == n,
                    forall|k: int| 0 <= k < i + j ==> 
                        result[k] == ((if k < i then 0 else c1[i] as int * c2[k - i] as int)) as i8,
                decreases c2.len() - j,
            {
                let idx = i + j;
                let product = (c1[i] as i32 * c2[j] as i32) as i32;
                result.set(idx, (result[idx] as i32 + product) as i8);
                j = j + 1;
            }
            i = i + 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}