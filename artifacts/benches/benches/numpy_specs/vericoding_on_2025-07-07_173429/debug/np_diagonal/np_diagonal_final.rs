use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn diagonal(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<i32>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(),
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -(arr.len() as i32) < k < (arr.len() as i32)
    ensures 
        ret.len() == if k > 0 { arr.len() - (k as usize) } else { arr.len() + ((-k) as usize) },
        forall|i: int| 0 <= i < ret.len() ==> {
            if k >= 0 {
                ret[i] == arr[i][(i + k)]
            } else {
                ret[i] == arr[(i - k)][i]
            }
        }
{
    let n = arr.len();
    let len = if k > 0 { n - (k as usize) } else { n + ((-k) as usize) };
    let mut ret = Vec::new();
    
    let mut i: usize = 0;
    while i < len {
        if k >= 0 {
            ret.push(arr[i][i + (k as usize)]);
        } else {
            ret.push(arr[i + ((-k) as usize)][i]);
        }
        i += 1;
    }
    ret
}

fn main() {}

}