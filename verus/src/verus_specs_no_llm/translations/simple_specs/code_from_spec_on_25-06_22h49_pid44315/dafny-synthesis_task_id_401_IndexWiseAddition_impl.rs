use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IndexWiseAddition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i).len() == b.spec_index(i).len()
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i).len() == a.spec_index(i).len(),
        forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result.spec_index(i).len() ==> result.spec_index(i).spec_index(j) == a.spec_index(i).spec_index(j) + b.spec_index(i).spec_index(j)
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.spec_index(k).len() == a.spec_index(k).len(),
            forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j < result.spec_index(k).len() ==> result.spec_index(k).spec_index(j) == a.spec_index(k).spec_index(j) + b.spec_index(k).spec_index(j)
    {
        let i_int = i as int;
        
        // Get the current rows
        let a_row = a.spec_index(i_int);
        let b_row = b.spec_index(i_int);
        let mut row = Seq::empty();
        let mut j: usize = 0;
        
        // Add assertions to help Verus understand the preconditions
        assert(i_int < a.len());
        assert(a_row.len() == b_row.len()) by {
            assert(a.spec_index(i_int).len() == b.spec_index(i_int).len());
        }
        
        while j < a_row.len()
            invariant
                0 <= j <= a_row.len(),
                a_row.len() == b_row.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row.spec_index(k) == a_row.spec_index(k) + b_row.spec_index(k),
                a_row == a.spec_index(i_int),
                b_row == b.spec_index(i_int),
                i_int < a.len(),
                i_int == i as int,
                0 <= i < a.len()
        {
            let j_int = j as int;
            
            // Compute the sum and add to the row
            let sum = a_row.spec_index(j_int) + b_row.spec_index(j_int);
            row = row.push(sum);
            
            // Help Verus understand that the pushed element has the correct value
            assert(row.spec_index(j_int) == sum);
            assert(row.spec_index(j_int) == a_row.spec_index(j_int) + b_row.spec_index(j_int));
            
            j = j + 1;
        }
        
        // Assertions to establish properties of the completed row
        assert(row.len() == a_row.len());
        assert(row.len() == a.spec_index(i_int).len());
        assert(forall|k: int| 0 <= k < row.len() ==> row.spec_index(k) == a.spec_index(i_int).spec_index(k) + b.spec_index(i_int).spec_index(k));
        
        // Add the row to the result
        result = result.push(row);
        
        // Help Verus understand the properties after pushing
        assert(result.len() == i + 1);
        assert(result.spec_index(i_int) == row);
        
        // Prove that the invariant is maintained
        assert(forall|k: int| 0 <= k < i ==> result.spec_index(k).len() == a.spec_index(k).len()) by {
            assert(forall|k: int| 0 <= k < i ==> result.spec_index(k) == old(result).spec_index(k));
        }
        
        assert(forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j < result.spec_index(k).len() ==> result.spec_index(k).spec_index(j) == a.spec_index(k).spec_index(j) + b.spec_index(k).spec_index(j)) by {
            assert(forall|k: int| 0 <= k < i ==> result.spec_index(k) == old(result).spec_index(k));
        }
        
        i = i + 1;
    }
    
    result
}

}