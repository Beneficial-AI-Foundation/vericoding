use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: usize = xs.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let seq_int: Seq<int> = xs@.map(|i: int, x: usize| i * (x as int)).skip(1);
    let seq_usize: Seq<usize> = seq_int.map_values(|x: int| x as usize);
    let res: Vec<usize> = Vec::from_seq(seq_usize);
    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}