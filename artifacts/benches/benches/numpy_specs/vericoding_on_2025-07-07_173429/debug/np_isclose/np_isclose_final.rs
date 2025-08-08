use vstd::prelude::*;

verus! {

fn np_isclose(a: &Vec<i32>, b: &Vec<i32>, tol: i32) -> (ret: Vec<bool>)
    requires
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] ret[i] == {
                let diff = a[i] - b[i];
                -tol < diff && diff < tol
            }
{
    let mut ret: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] ret[j] == {
                    let diff = a[j] - b[j];
                    -tol < diff && diff < tol
                }
        decreases a.len() - i
    {
        let diff = a[i] - b[i];
        let is_close = -tol < diff && diff < tol;
        ret.push(is_close);
        i = i + 1;
    }
    
    ret
}

}

fn main() {}