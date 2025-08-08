use vstd::prelude::*;

verus! {

fn diagonal(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<i32>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr.len(),
        -(#[verifier::truncate] (arr.len() as i32)) < k < #[verifier::truncate] (arr.len() as i32)
    ensures
        ret.len() == if k > 0 { arr.len() - k as usize } else { arr.len() + k },
        forall|i: int| 0 <= i < ret.len() ==> {
            ret[i] == if k >= 0 { 
                arr[i][i + k]
            } else { 
                arr[i - k][i] 
            }
        }
{
    let n = arr.len();
    let len = if k > 0 { 
        n - k as usize 
    } else { 
        (#[verifier::truncate] (n as i32) + k) as usize
    };
    
    let mut ret: Vec<i32> = Vec::new();
    
    for i in 0..len
        invariant
            forall|j: int| 0 <= j < i ==> {
                ret[j] == if k >= 0 { 
                    arr[j][j + k]
                } else { 
                    arr[j - k][j] 
                }
            }
    {
        if k >= 0 {
            let col_idx = i + k as usize;
            ret.push(arr[i][col_idx]);
        } else {
            let row_idx = i + ((-k) as usize);
            ret.push(arr[row_idx][i]);
        }
    }
    
    ret
}

}

fn main() {}