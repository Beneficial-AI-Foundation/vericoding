use vstd::prelude::*;

verus! {

fn reshape(arr: Vec<i32>, shape: Vec<i32>) -> (ret: Vec<Vec<i32>>)
    requires
        shape.len() == 2,
        forall|i: int| 0 <= i < 2 ==> shape[i] > 0 || shape[i] == -1,
        !(shape[0] == -1 && shape[1] == -1),
        if shape[0] > 0 && shape[1] > 0 {
            shape[0] * shape[1] == arr.len() as i32
        } else if shape[0] == -1 {
            arr.len() as i32 % shape[1] == 0 && shape[1] > 0
        } else {
            arr.len() as i32 % shape[0] == 0 && shape[0] > 0
        },
    ensures
        ret.len() == if shape[0] > 0 { 
            shape[0] as usize 
        } else { 
            arr.len() / (shape[1] as usize)
        },
        forall|i: int| #![auto] 0 <= i < ret.len() ==> 
            ret[i].len() == if shape[1] > 0 { 
                shape[1] as usize 
            } else { 
                arr.len() / (shape[0] as usize) 
            },
{
    let dim0: usize = if shape[0] > 0 {
        shape[0] as usize
    } else {
        arr.len() / (shape[1] as usize)
    };
    
    let dim1: usize = if shape[1] > 0 {
        shape[1] as usize
    } else {
        arr.len() / (shape[0] as usize)
    };

    let mut ret: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            ret.len() == i / dim1,
            dim1 > 0,
            forall|r: int| #![auto] 0 <= r < ret.len() ==> ret[r].len() == dim1,
        decreases arr.len() - i,
    {
        let row_idx = i / dim1;
        let col_idx = i % dim1;
        
        if col_idx == 0 {
            ret.push(Vec::new());
        }
        
        let ghost cur_row = ret.len() - 1;
        let mut last_row = ret.pop().unwrap();
        last_row.push(arr[i]);
        ret.push(last_row);
        
        i = i + 1;
    }
    
    ret
}

}

fn main() {}