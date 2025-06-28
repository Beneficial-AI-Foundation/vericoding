use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn counting_bits(n: int) -> (result: Vec<int>)
    requires
        0 <= n <= 100000
    ensures
        result.len() == n + 1,
        forall |i: int| 1 <= i < n + 1 ==> result.spec_index(i) == result.spec_index(i / 2) + i % 2
{
    let mut result = Vec::<int>::new();
    
    // Initialize with 0 for index 0
    result.push(0int);
    
    let mut i = 1int;
    while i <= n
        invariant
            0 <= i <= n + 1,
            result.len() == i,
            result.spec_index(0) == 0,
            forall |j: int| 1 <= j < i ==> result.spec_index(j) == result.spec_index(j / 2) + j % 2,
            forall |j: int| 1 <= j < i ==> 0 <= j / 2 < j,
            forall |j: int| 0 <= j < i ==> 0 <= result.spec_index(j)
    {
        proof {
            assert(i >= 1);
            assert(i / 2 >= 0) by {
                assert(i >= 1);
                assert(i / 2 >= 0);
            };
            assert(i / 2 < i) by {
                if i == 1 {
                    assert(i / 2 == 0);
                    assert(0 < 1);
                } else {
                    assert(i >= 2);
                    // For any integer i >= 2, i/2 < i
                    assert(2 * (i / 2) <= i) by {
                        // This is a property of integer division
                    };
                    if i % 2 == 0 {
                        assert(2 * (i / 2) == i);
                        assert(i / 2 == i / 2);
                        assert(i / 2 < i) by {
                            assert(i >= 2);
                            assert(i / 2 <= i / 2);
                            assert(i / 2 * 2 == i);
                            assert(i / 2 < i / 2 * 2);
                        };
                    } else {
                        assert(2 * (i / 2) == i - 1);
                        assert(i / 2 < i);
                    }
                }
            };
            assert(i / 2 < result.len()) by {
                assert(result.len() == i);
                assert(i / 2 < i);
            };
            assert(0 <= i / 2 < result.len());
        }
        
        // Convert to usize safely
        let half_index = i / 2;
        assert(0 <= half_index < result.len());
        let half_index_usize = half_index as usize;
        
        let bits_count = result.spec_index(half_index) + i % 2;
        result.push(bits_count);
        
        proof {
            assert(result.len() == i + 1);
            // The newly added element satisfies the property
            assert(result.spec_index(i) == bits_count);
            assert(bits_count == result.spec_index(i / 2) + i % 2);
            
            // All previous elements remain unchanged and still satisfy the property
            assert(forall |k: int| 0 <= k < i ==> result.spec_index(k) == old(result).spec_index(k));
            assert(forall |k: int| 1 <= k < i ==> result.spec_index(k) == result.spec_index(k / 2) + k % 2);
            
            // The new element also satisfies the property
            assert(result.spec_index(i) == result.spec_index(i / 2) + i % 2);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == n + 1);
        assert(result.len() == n + 1);
        assert(forall |j: int| 1 <= j < n + 1 ==> result.spec_index(j) == result.spec_index(j / 2) + j % 2);
    }
    
    result
}

}