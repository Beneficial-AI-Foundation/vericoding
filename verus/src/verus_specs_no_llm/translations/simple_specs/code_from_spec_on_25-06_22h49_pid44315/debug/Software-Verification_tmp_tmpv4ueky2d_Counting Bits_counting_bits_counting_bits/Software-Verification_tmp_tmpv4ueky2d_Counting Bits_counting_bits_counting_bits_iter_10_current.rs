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
    result.push(0);
    
    let mut i = 1;
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
            assert(i / 2 >= 0);
            assert(i / 2 < i) by {
                if i == 1 {
                    assert(i / 2 == 0);
                    assert(0 < 1);
                } else {
                    assert(i >= 2);
                    assert(i / 2 >= 1);
                    // For i >= 2, we have i / 2 < i
                    assert(i / 2 <= (i - 1));
                    assert(i / 2 < i);
                }
            };
            assert(i / 2 < result.len()) by {
                assert(result.len() == i);
                assert(i / 2 < i);
            };
        }
        
        // Safe conversion since we proved i / 2 < result.len() and result.len() fits in usize
        let half_index = (i / 2) as usize;
        
        proof {
            assert(0 <= i / 2 < result.len());
            assert(half_index == i / 2);
            assert(0 <= half_index < result.len());
        }
        
        let bits_count = result[half_index] + i % 2;
        result.push(bits_count);
        
        proof {
            assert(result.len() == i + 1);
            let old_result = old(result);
            
            // The new element satisfies the property
            assert(result.spec_index(i) == bits_count);
            assert(bits_count == old_result.spec_index(i / 2) + i % 2);
            assert(old_result.spec_index(i / 2) == result.spec_index(i / 2)) by {
                assert(forall |k: int| 0 <= k < i ==> old_result.spec_index(k) == result.spec_index(k));
            };
            assert(result.spec_index(i) == result.spec_index(i / 2) + i % 2);
            
            // All previous elements still satisfy the property
            assert(forall |k: int| 1 <= k < i + 1 ==> result.spec_index(k) == result.spec_index(k / 2) + k % 2) by {
                assert(forall |k: int| 1 <= k < i ==> old_result.spec_index(k) == old_result.spec_index(k / 2) + k % 2);
                assert(forall |k: int| 0 <= k < i ==> old_result.spec_index(k) == result.spec_index(k));
                assert(result.spec_index(i) == result.spec_index(i / 2) + i % 2);
            };
            
            // Bounds for division
            assert(forall |k: int| 1 <= k < i + 1 ==> 0 <= k / 2 < k) by {
                assert(forall |k: int| 1 <= k < i ==> 0 <= k / 2 < k);
                assert(i >= 1 ==> 0 <= i / 2 < i);
            };
            
            // Non-negativity
            assert(forall |k: int| 0 <= k < i + 1 ==> 0 <= result.spec_index(k)) by {
                assert(forall |k: int| 0 <= k < i ==> 0 <= old_result.spec_index(k));
                assert(forall |k: int| 0 <= k < i ==> old_result.spec_index(k) == result.spec_index(k));
                assert(0 <= result.spec_index(i / 2));
                assert(0 <= i % 2 <= 1);
                assert(result.spec_index(i) >= 0);
            };
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