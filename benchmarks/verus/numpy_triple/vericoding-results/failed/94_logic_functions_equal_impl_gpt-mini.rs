// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial reflexivity proof for bool equality */
fn bool_eq_reflexive(b: bool)
    ensures
        b == b,
{
    proof {
        assert(b == b);
    }
}

/* helper modified by LLM (iteration 5): convert Vec.len() to int in ghost */
fn vec_len_to_int<T>(v: &Vec<T>) -> int
    ensures
        result == v.len() as int,
{
    proof {
        result = v.len() as int;
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use tracked int indices for verification and usize for runtime indexing */
    let len_usize: usize = x1.len();
    let tracked len: int = len_usize as int;
    let mut res: Vec<bool> = Vec::new();
    let tracked mut i: int = 0;
    while i < len
        invariant
            0 <= i,
            i <= len,
            res.len() as int == i,
            forall|j: int| 0 <= j && j < i ==> res[j as usize] == (x1[j as usize] == x2[j as usize]),
        decreases
            len - i
    {
        let idx: usize = i as usize;
        let eq: bool = x1[idx] == x2[idx];
        res.push(eq);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}