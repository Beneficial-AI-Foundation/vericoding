// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute i8 modulo */
fn i8_mod(a: i8, b: i8) -> (res: i8)
    requires
        b != 0,
    ensures
        res == a % b,
{
    a % b
}

// </vc-helpers>

// <vc-spec>
fn remainder(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement remainder by iterating with int index and using i8_mod */
    let mut result = Vec::<i8>::new();
    let n = a.len();
    let n_int: int = n as int;
    let mut i: int = 0;
    while i < n_int
        invariant
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
            i <= n_int,
        decreases n_int - i
    {
        let ai: i8 = a[i as usize];
        let bi: i8 = b[i as usize];
        let r: i8 = i8_mod(ai, bi);
        result.push(r);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}