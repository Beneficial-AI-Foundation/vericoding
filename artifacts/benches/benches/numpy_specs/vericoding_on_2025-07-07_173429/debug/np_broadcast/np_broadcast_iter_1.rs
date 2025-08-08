use vstd::prelude::*;

verus! {

fn broadcast(a: &Vec<i32>, shape: &Vec<usize>) -> (ret: Vec<Vec<i32>>)
    requires 
        shape.len() == 2,
        shape[0] > 0,
        shape[1] > 0,
        shape[0] == a.len() || shape[1] == a.len(),
    ensures
        ret.len() == shape[0],
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].len() == shape[1],
        forall|i: int, j: int| 0 <= i < ret.len() && 0 <= j < shape[1] ==> {
            if shape[0] == a.len() {
                #[trigger] ret[i][j] == a[i]
            } else {
                #[trigger] ret[i][j] == a[j]
            }
        }
{
    let mut ret: Vec<Vec<i32>> = Vec::new();
    let shape0 = shape[0];
    let shape1 = shape[1];
    
    if shape0 == a.len() {
        // Broadcast along rows: each row gets the corresponding element from a
        let mut i: usize = 0;
        while i < shape0
            invariant
                i <= shape0,
                shape0 == a.len(),
                ret.len() == i,
                forall|ii: int| 0 <= ii < i ==> #[trigger] ret[ii].len() == shape1,
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < shape1 ==> 
                    #[trigger] ret[ii][jj] == a[ii]
            decreases shape0 - i
        {
            assert(i < a.len());
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < shape1
                invariant
                    i < a.len(),
                    j <= shape1,
                    row.len() == j,
                    forall|jj: int| 0 <= jj < j ==> #[trigger] row[jj] == a[i as int]
                decreases shape1 - j
            {
                row.push(a[i]);
                j = j + 1;
            }
            ret.push(row);
            i = i + 1;
        }
    } else {
        // Broadcast along columns: each column gets the corresponding element from a
        assert(shape1 == a.len());
        let mut i: usize = 0;
        while i < shape0
            invariant
                i <= shape0,
                shape1 == a.len(),
                ret.len() == i,
                forall|ii: int| 0 <= ii < i ==> #[trigger] ret[ii].len() == shape1,
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < shape1 ==> 
                    #[trigger] ret[ii][jj] == a[jj]
            decreases shape0 - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < shape1
                invariant
                    shape1 == a.len(),
                    j <= shape1,
                    row.len() == j,
                    forall|jj: int| 0 <= jj < j ==> #[trigger] row[jj] == a[jj]
                decreases shape1 - j
            {
                assert(j < a.len());
                row.push(a[j]);
                j = j + 1;
            }
            ret.push(row);
            i = i + 1;
        }
    }
    
    ret
}

}