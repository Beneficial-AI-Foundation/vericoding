use vstd::prelude::*;

verus! {

fn diagonal(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<i32>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (#[trigger] arr[i]).len() == arr.len(),
        -(arr.len() as i32) < k < (arr.len() as i32),
    ensures
        if k >= 0 {
            ret.len() == arr.len() - (k as usize)
        } else {
            ret.len() == arr.len() - ((-k) as usize)
        },
        forall|i: int| 0 <= i < ret.len() ==> {
            if k >= 0 {
                ret[i] == arr[i][i + k]
            } else {
                ret[i] == arr[i - k][i]
            }
        },
{
    let n = arr.len();
    let mut result = Vec::new();
    
    if k >= 0 {
        let k_u = k as usize;
        let mut i = 0usize;
        while i < n - k_u
            invariant
                0 <= i <= n - k_u,
                k >= 0,
                k_u == k,
                k_u < n,
                n == arr.len(),
                forall|row_idx: int| 0 <= row_idx < arr.len() ==> (#[trigger] arr[row_idx]).len() == arr.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    &&& #[trigger] result[j] == arr[j][j + k]
                },
            decreases n - k_u - i,
        {
            proof {
                assert(i < arr.len());
                assert(i + k_u < arr.len()) by {
                    assert(i < n - k_u);
                    assert(i + k_u < n);
                }
                assert(arr[i as int].len() == arr.len());
                assert(i + k_u < arr[i as int].len());
            }
            result.push(arr[i][i + k_u]);
            i += 1;
        }
    } else {
        let neg_k_u = (-k) as usize;
        let mut i = 0usize;
        while i < n - neg_k_u
            invariant
                0 <= i <= n - neg_k_u,
                k < 0,
                neg_k_u == (-k),
                neg_k_u < n,
                n == arr.len(),
                forall|row_idx: int| 0 <= row_idx < arr.len() ==> (#[trigger] arr[row_idx]).len() == arr.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    &&& #[trigger] result[j] == arr[j - k][j]
                },
            decreases n - neg_k_u - i,
        {
            proof {
                let src_row = i + neg_k_u;
                assert(src_row < arr.len()) by {
                    assert(i < n - neg_k_u);
                    assert(i + neg_k_u < n);
                }
                assert(arr[src_row as int].len() == arr.len());
                assert(i < arr[src_row as int].len());
            }
            result.push(arr[i + neg_k_u][i]);
            i += 1;
        }
    }
    
    result
}

}

fn main() {}