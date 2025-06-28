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
            forall |j: int| 1 <= j < i ==> result.spec_index(j) == result.spec_index(j / 2) + j % 2
    {
        proof {
            assert(i >= 1);
            assert(i / 2 >= 0);
            assert(i / 2 < i) by {
                assert(i >= 1);
                assert(i / 2 <= (i - 1) / 2);
                assert((i - 1) / 2 < i);
            };
            assert(i / 2 < result.len()) by {
                assert(result.len() == i);
                assert(i / 2 < i);
            };
        }
        let half_index = (i / 2) as usize;
        let bits_count = result[half_index] + i % 2;
        result.push(bits_count);
        
        proof {
            assert(result.len() == i + 1);
            assert(result.spec_index(i) == bits_count);
            assert(bits_count == result.spec_index(i / 2) + i % 2);
        }
        
        i = i + 1;
    }
    
    result
}

}