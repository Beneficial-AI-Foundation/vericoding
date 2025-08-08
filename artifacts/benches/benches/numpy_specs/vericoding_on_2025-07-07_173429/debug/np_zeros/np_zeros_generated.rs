use vstd::prelude::*;

verus! {

fn zeros(shape: &[usize]) -> (ret: Vec<Vec<i32>>)
    requires 
        shape.len() == 2,
        shape[0] > 0,
        shape[1] > 0,
    ensures
        ret.len() == shape[0],
        forall |i: int| 0 <= i < shape[0] ==> ret[i].len() == shape[1],
        forall |i: int, j: int| 0 <= i < shape[0] && 0 <= j < shape[1] ==> ret[i][j] == 0,
{
    let shape0 = shape[0];
    let shape1 = shape[1];
    let mut ret: Vec<Vec<i32>> = Vec::new();
    
    let mut i: usize = 0;
    while i < shape0
        invariant
            0 <= i <= shape0,
            ret.len() == i,
            forall |x: int| 0 <= x < i ==> ret[x].len() == shape1,
            forall |x: int, y: int| 0 <= x < i && 0 <= y < shape1 ==> ret[x][y] == 0,
        decreases shape0 - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < shape1
            invariant
                0 <= j <= shape1,
                row.len() == j,
                forall |y: int| 0 <= y < j ==> row[y] == 0,
            decreases shape1 - j,
        {
            row.push(0);
            j += 1;
        }
        
        ret.push(row);
        i += 1;
    }
    
    ret
}

fn main() {}

}