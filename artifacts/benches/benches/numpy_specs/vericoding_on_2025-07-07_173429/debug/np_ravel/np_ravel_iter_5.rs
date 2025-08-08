use vstd::prelude::*;

verus! {

fn ravel<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures 
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[i * arr[0].len() as int + j] == arr[i][j],
{
    let length0 = arr.len();
    let length1 = arr[0].len();
    let mut ret: Vec<T> = Vec::new();
    
    let mut row: usize = 0;
    while row < length0
        invariant
            row <= length0,
            ret.len() == row * length1,
            forall|i: int, j: int| 0 <= i < row && 0 <= j < length1 ==> 
                ret[i * length1 as int + j] == arr[i][j],
        decreases length0 - row,
    {
        let mut col: usize = 0;
        while col < length1
            invariant
                col <= length1,
                row < length0,
                ret.len() == row * length1 + col,
                forall|i: int, j: int| 0 <= i < row && 0 <= j < length1 ==> 
                    ret[i * length1 as int + j] == arr[i][j],
                forall|j: int| 0 <= j < col ==> 
                    ret[row as int * length1 as int + j] == arr[row as int][j],
            decreases length1 - col,
        {
            // Assert bounds verification equivalent to Dafny version
            assert(0 <= row < length0);
            assert(0 <= col < length1);
            assert(0 <= row * length1 + col);
            assert(row * length1 + col < length0 * length1);
            
            ret.push(arr[row][col]);
            col += 1;
        }
        row += 1;
    }
    
    ret
}

}

fn main() {
    println!("Verus ravel function compiled successfully!");
}