use vstd::prelude::*;

verus! {

fn tril(arr: Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>)
    requires 
        arr.len() > 0,
        arr@[0].len() > 0,
        arr.len() <= 100,
        arr@[0].len() <= 100,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr@[i].len() == arr@[0].len(),
        -200 <= k <= 200,
    ensures
        ret.len() == arr.len(),
        ret.len() > 0 ==> ret@[0].len() == arr@[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret@[i].len() == arr@[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr@[0].len() ==> 
            if j - i > k { 
                ret@[i]@[j] == 0 
            } else { 
                ret@[i]@[j] == arr@[i]@[j] 
            },
{
    let rows = arr.len();
    let cols = arr[0].len();
    
    let mut ret: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < rows
        invariant
            0 <= i <= rows,
            ret.len() == i,
            forall|ii: int| 0 <= ii < ret.len() ==> #[trigger] ret@[ii].len() == cols,
            forall|ii: int, jj: int| #![auto]
                0 <= ii < i && 0 <= jj < cols ==> 
                if jj - ii > k { 
                    ret@[ii]@[jj] == 0 
                } else { 
                    ret@[ii]@[jj] == arr@[ii]@[jj] 
                },
        decreases rows - i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                0 <= j <= cols,
                row.len() == j,
                i < rows,
                forall|jj: int| #![auto]
                    0 <= jj < j ==> 
                    if jj - (i as int) > k { 
                        row@[jj] == 0 
                    } else { 
                        row@[jj] == arr@[i as int]@[jj] 
                    },
            decreases cols - j
        {
            let j_i32 = j as i32;
            let i_i32 = i as i32;
            
            if j_i32 - i_i32 > k {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
            j = j + 1;
        }
        
        ret.push(row);
        i = i + 1;
    }
    
    ret
}

fn main() {}

}