use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasCommonElement(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a.spec_index(i) == b.spec_index(j),
        !result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a.spec_index(i) != b.spec_index(j)
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |ii: int, j: int| 0 <= ii < i && 0 <= j < b.len() ==> a.spec_index(ii) != b.spec_index(j)
    {
        let mut j = 0;
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                forall |ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a.spec_index(ii) != b.spec_index(jj),
                forall |jj: int| 0 <= jj < j ==> a.spec_index(i as int) != b.spec_index(jj)
        {
            if a[i] == b[j] {
                assert(a.spec_index(i as int) == b.spec_index(j as int));
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

}