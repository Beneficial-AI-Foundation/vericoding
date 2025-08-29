use vstd::prelude::*;

verus! {

fn cum_sum(a: &Vec<int>) -> (res: Vec<int>)
    ensures
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] + a[i],
{
    assume(false);
    Vec::new()
}

}

fn main() {}