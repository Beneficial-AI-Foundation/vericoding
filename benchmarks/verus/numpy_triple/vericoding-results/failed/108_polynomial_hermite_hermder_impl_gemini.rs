// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added missing decreases clause to the while loop */
fn hermder_once(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if c.len() <= 1 { 0 } else { c.len() - 1 },
        c.len() > 1 ==> forall|i: int| 0 <= i < result.len() ==>
            result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
{
    if c.len() <= 1 {
        return Vec::new();
    }
    let n = c.len() - 1;
    let mut der = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            der.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> 
                der[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1]
        decreases n - i
    {
        let val = scl * (2 * ((i as i32) + 1));
        let temp = val * c[i + 1];
        der.push(temp);
        i = i + 1;
    }
    der
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): swapped order of invariant and decreases clauses to fix compilation error. */
    if m >= c.len() {
        return Vec::new();
    }

    let mut temp_c = c;
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            // When m < c.len() initially, the length of temp_c will be > 1
            // for each iteration, so it decreases by exactly 1.
            m < c.len() ==> temp_c.len() == c.len() - i as nat,

            // This invariant is needed to prove the m=2 case. It captures the state of 
            // temp_c after one differentiation and relates it to the original vector `c`.
            (m == 2 && i == 1 && m < c.len()) ==> (
                forall|k: int| 0 <= k < temp_c.len() ==> 
                    temp_c[k] == scl * (2 * ((k + 1) as i32)) * c[k + 1]
            )
        decreases m - i
    {
        temp_c = hermder_once(temp_c, scl);
        i = i + 1;
    }

    temp_c
}
// </vc-code>

}
fn main() {}