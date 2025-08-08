use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn transpose<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<Vec<T>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr@[i].len() == arr@[0].len(),
    ensures 
        ret.len() == arr@[0].len(),
        ret.len() > 0 ==> ret@[0].len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr@[0].len() ==> 
            ret@[j]@[i] == arr@[i]@[j],
{
    if arr.len() == 0 || arr[0].len() == 0 {
        return Vec::new();
    }
    
    let rows = arr.len();
    let cols = arr[0].len();
    
    let mut ret: Vec<Vec<T>> = Vec::new();
    
    let mut j: usize = 0;
    while j < cols
        invariant
            0 <= j <= cols,
            ret.len() == j,
            rows == arr.len(),
            forall|k: int| #![auto] 0 <= k < j ==> ret@[k].len() == rows,
            forall|i: int, k: int| #![auto] 0 <= i < rows && 0 <= k < j ==>
                ret@[k]@[i] == arr@[i]@[k],
        decreases cols - j,
    {
        let mut row: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                row.len() == i,
                forall|k: int| #![auto] 0 <= k < i ==> row@[k] == arr@[k]@[j as int],
            decreases rows - i,
        {
            assert(i < arr.len());
            assert((j as int) < arr@[i as int].len()) by {
                assert(arr@[i as int].len() == arr@[0].len());
                assert((j as int) < (cols as int));
                assert((cols as int) == arr@[0].len());
            };
            row.push(arr[i][j]);
            i += 1;
        }
        ret.push(row);
        j += 1;
    }
    
    ret
}

fn main() {}

}