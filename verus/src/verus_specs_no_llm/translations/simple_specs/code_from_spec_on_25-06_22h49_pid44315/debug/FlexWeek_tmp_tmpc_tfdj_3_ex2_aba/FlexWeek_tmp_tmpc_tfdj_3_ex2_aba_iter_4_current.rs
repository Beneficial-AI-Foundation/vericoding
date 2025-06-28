use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn aba(a: Vec<int>) -> (b: Vec<int>)
    ensures
        a.len() == b.len(), // needed for next line,
        forall|x: int| 0 <= x < b.len() ==> b.spec_index(x) == abs(a.spec_index(x))
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == abs(a.spec_index(j))
    {
        let abs_val = if a[i] < 0 { -a[i] } else { a[i] };
        result.push(abs_val);
        
        assert(result.len() == i + 1);
        assert(result.spec_index(i as int) == abs_val);
        assert(abs_val == abs(a.spec_index(i as int)));
        
        i += 1;
    }
    
    assert(i == a.len());
    assert(result.len() == a.len());
    
    // Final assertion to help prove the postcondition
    assert(forall|x: int| 0 <= x < result.len() ==> result.spec_index(x) == abs(a.spec_index(x)));
    
    result
}

}