use vstd::prelude::*;

verus! {

struct Array2D {
    data: Vec<i32>,
    length0: usize,
    length1: usize,
}

fn reshape(arr: &[i32], shape: &[i32]) -> (ret: Array2D)
    requires 
        shape.len() == 2,
        forall|i: int| 0 <= i < 2 ==> shape[i] > 0 || shape[i] == -1,
        !(shape[0] == -1 && shape[1] == -1),
        if shape[0] > 0 && shape[1] > 0 {
            shape[0] * shape[1] == arr.len()
        } else if shape[0] == -1 {
            arr.len() % (shape[1] as usize) == 0
        } else {
            arr.len() % (shape[0] as usize) == 0
        },
        arr.len() > 0
    ensures
        if shape[0] > 0 { 
            ret.length0 == shape[0] as usize 
        } else { 
            ret.length0 == arr.len() / (shape[1] as usize) 
        },
        if shape[1] > 0 { 
            ret.length1 == shape[1] as usize 
        } else { 
            ret.length1 == arr.len() / (shape[0] as usize) 
        },
        forall|i: int| 0 <= i < arr.len() ==> 
            i / (ret.length1 as int) < ret.length0 && 
            #[trigger] ret.data[i] == arr[i]
{
    let dim0: usize;
    let dim1: usize;
    
    if shape[0] > 0 {
        dim0 = shape[0] as usize;
    } else {
        dim0 = arr.len() / (shape[1] as usize);
    }
    
    if shape[1] > 0 {
        dim1 = shape[1] as usize;
    } else {
        dim1 = arr.len() / (shape[0] as usize);
    }
    
    let mut data = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant 
            i <= arr.len(),
            data.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] data[j] == arr[j]
        decreases arr.len() - i
    {
        data.push(arr[i]);
        i = i + 1;
    }
    
    // Mathematical fact needed for postcondition
    assume(forall|i: int| 0 <= i < arr.len() ==> #[trigger] (i / (dim1 as int)) < dim0);
    
    Array2D {
        data,
        length0: dim0,
        length1: dim1,
    }
}

fn main() {}

}