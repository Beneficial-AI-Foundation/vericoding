use vstd::prelude::*;

verus! {

fn reshape(arr: &Vec<i32>, shape: &Vec<i32>) -> (ret: Vec<Vec<i32>>)
    requires
        shape.len() == 2,
        shape[0] > 0 || shape[0] == -1,
        shape[1] > 0 || shape[1] == -1,
        !(shape[0] == -1 && shape[1] == -1),
        if shape[0] > 0 && shape[1] > 0 {
            shape[0] as int * shape[1] as int == arr.len() as int
        } else if shape[0] == -1 {
            shape[1] > 0 && arr.len() as int % shape[1] as int == 0
        } else {
            shape[0] > 0 && arr.len() as int % shape[0] as int == 0
        },
        arr.len() > 0,
    ensures
        if shape[0] > 0 {
            ret.len() == shape[0] as usize
        } else {
            ret.len() == (arr.len() as int / shape[1] as int) as usize
        },
        forall|i: int| 0 <= i < ret.len() as int ==> {
            if shape[1] > 0 {
                ret[i].len() == shape[1] as usize
            } else {
                ret[i].len() == (arr.len() as int / shape[0] as int) as usize
            }
        },
        forall|i: int| 0 <= i < arr.len() as int ==> {
            let length1 = if shape[1] > 0 { shape[1] as int } else { arr.len() as int / shape[0] as int };
            let row = i / length1;
            let col = i % length1;
            row < ret.len() as int && col < ret[row].len() as int && ret[row][col] == arr[i]
        },
{
    let length1 = if shape[1] > 0 { 
        shape[1] as usize 
    } else { 
        (arr.len() / shape[0] as usize) 
    };
    let length0 = if shape[0] > 0 { 
        shape[0] as usize 
    } else { 
        (arr.len() / shape[1] as usize) 
    };
    
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    
    while i < length0
        invariant
            i <= length0,
            result.len() == i,
        decreases length0 - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0usize;
        
        while j < length1
            invariant
                j <= length1,
                row.len() == j,
            decreases length1 - j,
        {
            let idx_usize = i * length1 + j;
            if idx_usize < arr.len() {
                row.push(arr[idx_usize]);
            }
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}

fn main() {}

}