use vstd::prelude::*;

verus! {

fn diagonal(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<i32>)
    requires
        arr.len() > 0,
        arr.len() == arr[0].len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr.len(),
        -(arr.len() as i32) < k < arr.len() as i32,
        arr.len() <= i32::MAX,
    ensures
        if k > 0 { ret.len() == arr.len() - k } else { ret.len() == arr.len() + k },
        forall|i: int| 0 <= i < ret.len() ==> 
            if k >= 0 { 
                ret[i] == arr[i][i + k] 
            } else { 
                ret[i] == arr[i - k][i] 
            },
{
    let n = arr.len() as i32;
    let len_val = if k > 0 { n - k } else { n + k };
    let mut ret = Vec::<i32>::new();
    
    let mut i: i32 = 0;
    while i < len_val
        invariant 
            0 <= i <= len_val,
            ret.len() == i,
            len_val == if k > 0 { n - k } else { n + k },
            n == arr.len(),
            forall|j: int| 0 <= j < i ==> 
                if k >= 0 { 
                    ret[j] == arr[j][j + k] 
                } else { 
                    ret[j] == arr[j - k][j] 
                },
        decreases len_val - i,
    {
        if k >= 0 {
            // For positive k, we extract diagonal from (0,k) to (n-k-1, n-1)
            // Row: i ranges 0 to n-k-1, Col: i+k ranges k to n-1
            ret.push(arr[i as usize][(i + k) as usize]);
        } else {
            // For negative k, we extract diagonal from (-k,0) to (n-1, n+k-1)  
            // Row: i-k ranges -k to n-1, Col: i ranges 0 to n+k-1
            ret.push(arr[(i - k) as usize][i as usize]);
        }
        i = i + 1;
    }
    
    ret
}

fn main() {}

}