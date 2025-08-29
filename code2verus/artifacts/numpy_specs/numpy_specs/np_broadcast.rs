use vstd::prelude::*;

verus! {

// External specification - mirrors the original Dafny method
#[verifier::external_body]
fn broadcast(a: Vec<i32>, shape: Vec<usize>) -> (ret: Vec<Vec<i32>>)
    requires 
        shape.len() == 2,
        shape[0] == a.len() || shape[1] == a.len(),
    ensures 
        ret.len() == shape[0],
        forall|i: int| #![auto] 0 <= i < ret.len() ==> ret[i].len() == shape[1],
        forall|i: int, j: int| #![auto] 0 <= i < shape[0] && 0 <= j < shape[1] ==> {
            if shape[0] == a.len() {
                ret[i][j] == a[i]
            } else {
                ret[i][j] == a[j]
            }
        },
{
    Vec::new()
}

fn main() {}

}