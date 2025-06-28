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
    let mut result = Vec::new();
    
    // Initialize with 0 for index 0
    result.push(0);
    
    let mut i = 1;
    while i <= n
        invariant
            0 <= i <= n + 1,
            result.len() == i,
            result.spec_index(0) == 0,
            forall |j: int| 1 <= j < i ==> result.spec_index(j) == result.spec_index(j / 2) + j % 2
    {
        let bits_count = result.spec_index(i / 2) + i % 2;
        result.push(bits_count);
        i = i + 1;
    }
    
    result
}

}