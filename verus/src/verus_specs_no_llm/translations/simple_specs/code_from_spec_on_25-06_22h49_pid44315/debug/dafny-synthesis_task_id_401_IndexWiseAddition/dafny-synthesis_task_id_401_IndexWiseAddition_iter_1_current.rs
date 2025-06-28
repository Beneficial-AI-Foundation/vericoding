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
        forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result.spec_index(i).len() ==> result.spec_index(i)[j] == a.spec_index(i)[j] + b.spec_index(i)[j]
{
    let mut result = Seq::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.spec_index(k).len() == a.spec_index(k).len(),
            forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j < result.spec_index(k).len() ==> result.spec_index(k)[j] == a.spec_index(k)[j] + b.spec_index(k)[j]
    {
        let mut row = Seq::empty();
        let mut j = 0;
        let a_row = a.spec_index(i as int);
        let b_row = b.spec_index(i as int);
        
        while j < a_row.len()
            invariant
                0 <= j <= a_row.len(),
                a_row.len() == b_row.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row.spec_index(k) == a_row.spec_index(k) + b_row.spec_index(k)
        {
            let sum = a_row.spec_index(j as int) + b_row.spec_index(j as int);
            row = row.push(sum);
            j = j + 1;
        }
        
        result = result.push(row);
        i = i + 1;
    }
    
    result
}

}