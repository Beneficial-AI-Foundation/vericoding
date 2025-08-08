use vstd::prelude::*;

verus! {

fn broadcast(a: &[i32], shape: &[usize]) -> (ret: Vec<Vec<i32>>)
    requires 
        shape.len() == 2,
        shape[0] == a.len() || shape[1] == a.len(),
    ensures
        ret.len() == shape[0],
        forall|i: int| #![auto] 0 <= i < shape[0] as int ==> ret@[i].len() == shape[1],
        forall|i: int, j: int| #![auto] 0 <= i < shape[0] as int && 0 <= j < shape[1] as int ==> {
            if shape[0] == a.len() {
                ret@[i]@[j] == a@[i]
            } else {
                ret@[i]@[j] == a@[j]
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
                ret.len() == i,
                i <= shape0,
                shape0 == a.len(),
                forall|ii: int| #![auto] 0 <= ii < i as int ==> ret@[ii].len() == shape1,
                forall|ii: int, jj: int| #![auto] 0 <= ii < i as int && 0 <= jj < shape1 as int ==> 
                    ret@[ii]@[jj] == a@[ii],
            decreases shape0 - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < shape1
                invariant
                    row.len() == j,
                    j <= shape1,
                    i < a.len(),
                    forall|jj: int| #![auto] 0 <= jj < j as int ==> row@[jj] == a@[i as int],
                decreases shape1 - j
            {
                row.push(a[i]);
                j += 1;
            }
            ret.push(row);
            i += 1;
        }
    } else {
        // shape1 == a.len() from precondition
        assert(shape1 == a.len());
        // Broadcast along columns: each column gets the corresponding element from a
        let mut i: usize = 0;
        while i < shape0
            invariant
                ret.len() == i,
                i <= shape0,
                shape1 == a.len(),
                forall|ii: int| #![auto] 0 <= ii < i as int ==> ret@[ii].len() == shape1,
                forall|ii: int, jj: int| #![auto] 0 <= ii < i as int && 0 <= jj < shape1 as int ==> 
                    ret@[ii]@[jj] == a@[jj],
            decreases shape0 - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < shape1
                invariant
                    row.len() == j,
                    j <= shape1,
                    shape1 == a.len(),
                    forall|jj: int| #![auto] 0 <= jj < j as int ==> row@[jj] == a@[jj],
                decreases shape1 - j
            {
                row.push(a[j]);
                j += 1;
            }
            ret.push(row);
            i += 1;
        }
    }
    
    ret
}

fn main() {}

}