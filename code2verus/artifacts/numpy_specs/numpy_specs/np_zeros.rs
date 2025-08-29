use vstd::prelude::*;

verus! {

// Define a 2D array structure
pub struct Array2<T> {
    pub data: Vec<Vec<T>>,
    pub length0: usize,
    pub length1: usize,
}

impl<T> Array2<T> {
    pub open spec fn get(self, i: int, j: int) -> T
        recommends 
            0 <= i < self.length0,
            0 <= j < self.length1,
            0 <= i < self.data.len(),
            0 <= j < self.data[i as int].len(),
    {
        self.data[i as int][j as int]
    }
}

fn zeros(shape: &Vec<usize>) -> (ret: Array2<i32>)
    requires 
        shape.len() == 2,
        shape[0] > 0,
        shape[1] > 0,
    ensures 
        ret.length0 == shape[0],
        ret.length1 == shape[1],
        ret.data.len() == shape[0],
        forall|i: int| #![auto] 0 <= i < shape[0] ==> ret.data[i as int].len() == shape[1],
        forall|i: int, j: int| 0 <= i < shape[0] && 0 <= j < shape[1] ==> ret.get(i, j) == 0,
{
    let mut data: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    let shape0 = shape[0];
    let shape1 = shape[1];
    
    while i < shape0
        invariant
            i <= shape0,
            data.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> data[k as int].len() == shape1,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < shape1 ==> data[k as int][l as int] == 0,
        decreases shape0 - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < shape1
            invariant
                j <= shape1,
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l as int] == 0,
            decreases shape1 - j,
        {
            row.push(0);
            j += 1;
        }
        
        data.push(row);
        i += 1;
    }
    
    Array2 {
        data,
        length0: shape0,
        length1: shape1,
    }
}

fn main() {}

}