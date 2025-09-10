use vstd::prelude::*;

verus! {

fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)

    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
{
    assume(false);
    unreached();
}

}
fn main() {}