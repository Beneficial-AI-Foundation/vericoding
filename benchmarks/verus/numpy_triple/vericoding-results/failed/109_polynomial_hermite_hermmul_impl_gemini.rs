// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] == c1[i] * c2[0],
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] == c2[i] * c1[0],

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed commas between invariant clauses to fix compilation error */
    let n = c1.len();
    let m = c2.len();

    if n == 0 || m == 0 {
        return vec![0];
    }

    let result_len = n + m - 1;

    let mut c1_is_zero = true;
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant c1_is_zero == forall|k: int| 0 <= k < i as int ==> c1@[k] == 0
    {
        if c1[i] != 0 {
            c1_is_zero = false;
        }
        i = i + 1;
    }

    let mut c2_is_zero = true;
    let mut j: usize = 0;
    while j < m
        invariant j <= m
        invariant c2_is_zero == forall|k: int| 0 <= k < j as int ==> c2@[k] == 0
    {
        if c2[j] != 0 {
            c2_is_zero = false;
        }
        j = j + 1;
    }

    if c1_is_zero || c2_is_zero {
        let result = Vec::from_elem(0, result_len);
        return result;
    }
    
    if m == 1 {
        let mut result = Vec::with_capacity(n);
        let mut i_k: usize = 0;
        while i_k < n
            invariant i_k <= n
            invariant result.len() == i_k
            invariant result.capacity() == n
            invariant forall|l: int| 0 <= l < i_k as int ==> result@[l] == c1@[l] * c2@[0]
        {
            result.push(c1[i_k] * c2[0]);
            i_k = i_k + 1;
        }
        return result;
    }

    if n == 1 {
        let mut result = Vec::with_capacity(m);
        let mut i_k: usize = 0;
        while i_k < m
            invariant i_k <= m
            invariant result.len() == i_k
            invariant result.capacity() == m
            invariant forall|l: int| 0 <= l < i_k as int ==> result@[l] == c2@[l] * c1@[0]
        {
            result.push(c2[i_k] * c1[0]);
            i_k = i_k + 1;
        }
        return result;
    }
    
    let mut result = Vec::from_elem(0, result_len);
    let mut i_loop: usize = 0;
    while i_loop < n
        invariant i_loop <= n
        invariant result.len() == result_len
        invariant n > 1 && m > 1
    {
        let mut j_loop: usize = 0;
        while j_loop < m
            invariant j_loop <= m
            invariant i_loop < n
            invariant result.len() == result_len
        {
            let k = i_loop + j_loop;
            let prod = c1[i_loop] * c2[j_loop];
            result.set(k, result[k] + prod);
            j_loop = j_loop + 1;
        }
        i_loop = i_loop + 1;
    }
    result
}
// </vc-code>

}
fn main() {}