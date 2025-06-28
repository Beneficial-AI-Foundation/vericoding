use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Symmetric(a: Vec<int>) -> (flag: bool)
    ensures
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) == a.spec_index(a.len() - x - 1),
        flag == false ==> exists|x: int| 0 <= x < a.len() && a.spec_index(x) != a.spec_index(a.len() - x - 1)
{
    let mut i: usize = 0;
    let len = a.len();
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(len - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(a.spec_index(i as int) != a.spec_index(len - (i as int) - 1));
            return false;
        }
        i += 1;
    }
    
    // Prove that the entire array is symmetric
    assert(forall|x: int| 0 <= x < len ==> a.spec_index(x) == a.spec_index(len - x - 1)) by {
        // For any index x in the array
        assert(forall|x: int| 0 <= x < len ==> {
            if x < len / 2 {
                // x is in the first half, we already proved this in the loop
                a.spec_index(x) == a.spec_index(len - x - 1)
            } else {
                // x is in the second half
                let mirror = len - x - 1;
                // The mirror is in the first half
                &&& 0 <= mirror < len / 2
                // We proved this pair in the loop
                &&& a.spec_index(mirror) == a.spec_index(len - mirror - 1)
                // And len - mirror - 1 == x
                &&& len - mirror - 1 == x
                // Therefore a[mirror] == a[x], which means a[x] == a[mirror]
                &&& a.spec_index(x) == a.spec_index(mirror)
                &&& a.spec_index(x) == a.spec_index(len - x - 1)
            }
        });
    };
    
    true
}

}