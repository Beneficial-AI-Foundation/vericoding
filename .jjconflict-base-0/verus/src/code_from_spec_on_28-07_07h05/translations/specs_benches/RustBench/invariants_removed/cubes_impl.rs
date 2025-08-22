use vstd::prelude::*;

verus! {

//ATOM
#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    a + b
}

//IMPL cubes
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == j * j * j,
            i <= len,
        decreases len - i
    {
        /* code modified by LLM (iteration 1): use i32 arithmetic to avoid usize overflow */
        let i_i32 = i as i32;
        let cube = i_i32 * i_i32 * i_i32;
        /* code modified by LLM (iteration 1): add assertion to connect i32 and int arithmetic */
        assert(cube == (i as int) * (i as int) * (i as int));
        result.push(cube);
        i += 1;
    }
    
    result
}

fn main() {}
}