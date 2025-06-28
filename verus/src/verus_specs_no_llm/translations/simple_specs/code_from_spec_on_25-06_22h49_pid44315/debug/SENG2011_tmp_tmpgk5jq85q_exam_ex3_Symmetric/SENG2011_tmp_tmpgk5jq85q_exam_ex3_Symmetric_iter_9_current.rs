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
            i <= len,
            len == a.len(),
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(a.len() - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(exists|x: int| 0 <= x < a.len() && a.spec_index(x) != a.spec_index(a.len() - x - 1)) by {
                assert(0 <= i < len);
                assert(0 <= i as int < a.len());
                assert(0 <= a.len() - (i as int) - 1 < a.len());
                assert(a.spec_index(i as int) != a.spec_index(a.len() - (i as int) - 1));
            }
            return false;
        }
        i += 1;
    }
    
    // Prove that the entire array is symmetric
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) == a.spec_index(a.len() - x - 1)) by {
        assert(forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(a.len() - x - 1));
        assert(i as int >= a.len() / 2);
        
        forall|x: int| 0 <= x < a.len() implies {
            let mirror_x = a.len() - x - 1;
            assert(0 <= mirror_x < a.len());
            
            if x < a.len() / 2 {
                // x is in the first half, we already proved this in the loop
                assert(x < i as int);
                assert(a.spec_index(x) == a.spec_index(a.len() - x - 1));
            } else {
                // x is in the second half, use symmetry of what we already proved
                assert(mirror_x < a.len() / 2);
                assert(mirror_x < i as int);
                // We know a[mirror_x] == a[len - mirror_x - 1]
                // And len - mirror_x - 1 == len - (len - x - 1) - 1 == x
                assert(a.len() - mirror_x - 1 == x);
                assert(a.spec_index(mirror_x) == a.spec_index(x));
                assert(a.spec_index(x) == a.spec_index(mirror_x));
                assert(a.spec_index(x) == a.spec_index(a.len() - x - 1));
            }
        }
    }
    
    true
}

}