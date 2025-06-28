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
    let half_len = len / 2;
    
    while i < half_len
        invariant
            0 <= i <= half_len,
            half_len == len / 2,
            len == a.len(),
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(a.len() - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(exists|x: int| 0 <= x < a.len() && a.spec_index(x) != a.spec_index(a.len() - x - 1)) by {
                assert(0 <= i < len);
                assert(len - i - 1 < len);
                assert(a.spec_index(i as int) != a.spec_index(a.len() - (i as int) - 1));
            }
            return false;
        }
        i += 1;
    }
    
    // Prove that the entire array is symmetric
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) == a.spec_index(a.len() - x - 1)) by {
        forall|x: int| 0 <= x < a.len() implies {
            let mirror_x = a.len() - x - 1;
            assert(0 <= mirror_x < a.len());
            
            if x <= a.len() / 2 - 1 {
                // x is in the first half, we proved this in the loop
                assert(x < i as int) by {
                    assert(i == half_len);
                    assert(half_len == len / 2);
                    assert(x <= a.len() / 2 - 1);
                    assert(x < a.len() / 2);
                }
                assert(a.spec_index(x) == a.spec_index(a.len() - x - 1));
            } else {
                // x is in the second half, use symmetry
                assert(x >= a.len() / 2);
                assert(mirror_x < a.len() / 2) by {
                    assert(mirror_x == a.len() - x - 1);
                    assert(x >= a.len() / 2);
                    assert(a.len() - x <= a.len() / 2);
                    assert(mirror_x < a.len() / 2);
                }
                assert(mirror_x < i as int) by {
                    assert(i == half_len);
                    assert(half_len == len / 2);
                    assert(mirror_x < a.len() / 2);
                }
                // We know a[mirror_x] == a[len - mirror_x - 1] from the loop
                // And len - mirror_x - 1 == x
                assert(a.len() - mirror_x - 1 == x) by {
                    assert(mirror_x == a.len() - x - 1);
                    assert(a.len() - (a.len() - x - 1) - 1 == x);
                }
                assert(a.spec_index(mirror_x) == a.spec_index(a.len() - mirror_x - 1));
                assert(a.spec_index(mirror_x) == a.spec_index(x));
                assert(a.spec_index(x) == a.spec_index(a.len() - x - 1));
            }
        }
    }
    
    true
}

}