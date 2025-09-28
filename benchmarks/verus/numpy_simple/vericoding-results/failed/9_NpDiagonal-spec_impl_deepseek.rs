// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

type SeqOfSeq<T> = Seq<Seq<T>>;

proof fn abs(n: i8) -> (result: nat)
    ensures
        result == (if n >= 0 { n as nat } else { (-n) as nat })
{
    if n < 0 {
        (-n) as nat
    } else {
        n as nat
    }
}

proof fn square_matrix_diagonal_helper(arr: SeqOfSeq<i8>, k: i8) -> (result: Seq<i8>)
    requires
        arr.len() > 0,
        arr.len() <= 0xffffffff,
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -((arr.len() as i8)) < k && k < (arr.len() as i8)
    ensures
        if k > 0 {
            result.len() == (arr.len() as i8 - k) as usize &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i]@[(i as i8 + k) as usize]
        } else {
            result.len() == (arr.len() as i8 + (-k)) as usize &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[(i as i8 + (-k)) as usize]@[i]
        }
{
    let len = arr.len() as i8;
    let start_row = if k > 0 { 0 } else { -k };
    let start_col = if k > 0 { k } else { 0 };
    let count = len - (if k >= 0 { k } else { -k });
    
    assert(count > 0);
    
    let mut i: i8 = 0;
    let mut result_seq = Seq::empty();
    
    while i < count
        invariant
            i >= 0,
            i <= count,
            result_seq.len() == i as usize,
            forall|j: int| 0 <= j < result_seq.len() ==> {
                let row = start_row + j as i8;
                let col = start_col + j as i8;
                result_seq[j] == arr[row as usize]@[col as usize]
            }
        decreases count - i
    {
        let row = (start_row + i) as usize;
        let col = (start_col + i) as usize;
        
        result_seq = result_seq.push(arr[row]@[col]);
        i = i + 1;
    }
    
    result_seq
}

// </vc-helpers>

// <vc-spec>
/* Matrix type represented as a 2D vector */
type Matrix<T> = Vec<Vec<T>>;

fn diagonal(arr: Matrix<i8>, k: i8) -> (result: Vec<i8>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(), /* square matrix */
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -(arr.len() as i8) < k && k < (arr.len() as i8),
    ensures
        if k > 0 {
            result.len() == arr.len() - (k as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i][i + (k as usize)]
        } else {
            result.len() == arr.len() + ((-k) as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i + ((-k) as usize)][i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversion from usize to int in sequence indexing */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let len = arr.len();
    
    if k > 0 {
        let count: usize = (len as i8 - k) as usize;
        assert(count <= len);
        
        while i < count
            invariant
                i <= count,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    result@[j] == arr@[j]@[(j as i8 + k) as usize]
                }
        {
            let val = arr@[i]@[(i as i8 + k) as usize];
            result.push(val);
            i = i + 1;
        }
    } else {
        let k_abs = (-k) as usize;
        let count: usize = len + k_abs;
        assert(count <= len);
        
        while i < count
            invariant
                i <= count,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    result@[j] == arr@[(j + k_abs)]@[j]
                }
        {
            let val = arr@[(i + k_abs)]@[i];
            result.push(val);
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}