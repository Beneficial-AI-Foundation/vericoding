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
    let len = a.len();
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(len as int - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(exists|x: int| 0 <= x < len && a.spec_index(x) != a.spec_index(len as int - x - 1)) by {
                assert(0 <= i < len);
                assert(a.spec_index(i as int) != a.spec_index(len as int - (i as int) - 1));
            }
            return false;
        }
        i += 1;
    }
    
    // Prove that the entire array is symmetric
    assert(forall|x: int| 0 <= x < len ==> a.spec_index(x) == a.spec_index(len as int - x - 1)) by {
        forall|x: int| 0 <= x < len implies {
            if x < len as int / 2 {
                // x is in the first half, we already proved this in the loop
                assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
            } else {
                // x is in the second half or middle
                let mirror = len as int - x - 1;
                if mirror < len as int / 2 {
                    // The mirror is in the first half, so we proved this pair
                    assert(a.spec_index(mirror) == a.spec_index(len as int - mirror - 1));
                    // And len - mirror - 1 == x
                    assert(len as int - mirror - 1 == x);
                    // Therefore a[mirror] == a[x], which means a[x] == a[mirror]
                    assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
                } else {
                    // This is the middle element case (x == mirror)
                    assert(x == len as int - x - 1);
                    assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
                }
            }
        }
    };
    
    true
}

}