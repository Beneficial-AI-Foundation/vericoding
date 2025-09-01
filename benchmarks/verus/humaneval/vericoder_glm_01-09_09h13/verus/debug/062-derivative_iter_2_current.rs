use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_derivative_properties(xs: &Vec<usize>)
    ensures
        xs@.len() == 0 || xs@.map(|i: int, x: usize| (i * (x as int))).skip(1)
            =~= (0..xs@.len() - 1).map(|i: int| *(&xs@[i+1]) as int * (i+1))
{
    if xs@.len() == 0 {
        assert(xs@.map(|i: int, x: usize| (i * (x as int))).skip(1).seq_len() == 0);
        assert((0..xs@.len() - 1).map(|i: int| *(&xs@[i+1]) as int * (i+1)).seq_len() == 0);
    } else {
        assert(xs@.map(|i: int, x: usize| (i * (x as int))).skip(1)
            =~= (1..xs@.len()).map(|i: int| *(&xs@[i]) as int * i));
        assert((1..xs@.len()).map(|i: int| *(&xs@[i]) as int * i)
            =~= (0..xs@.len() - 1).map(|i: int| *(&xs@[i+1]) as int * (i+1)));
    }
}
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
    if xs.len() == 0 {
        None
    } else {
        let mut ret = Vec::with_capacity((xs.len() - 1) as usize);
        proof {
            lemma_derivative_properties(xs);
        }
        for i in 0..xs.len() - 1
            invariant
                ret@.len() == i,
                ret@ =~= (0..i).map(|j: int| *(&xs@[j+1]) as int * (j+1))
        {
            ret.push((xs@[i+1] * (i+1)) as usize);
        }
        Some(ret)
    }
}
// </vc-code>

fn main() {}
}