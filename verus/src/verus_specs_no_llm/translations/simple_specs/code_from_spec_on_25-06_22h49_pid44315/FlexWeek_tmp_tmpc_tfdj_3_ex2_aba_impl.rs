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
        let val = a[i];
        let abs_val = if val >= 0 { val } else { -val };
        
        // Prove that abs_val equals abs(a.spec_index(i as int)) before pushing
        assert(val == a.spec_index(i as int));
        assert(abs_val == abs(a.spec_index(i as int))) by {
            if val >= 0 {
                assert(abs_val == val);
                assert(abs(a.spec_index(i as int)) == a.spec_index(i as int));
            } else {
                assert(abs_val == -val);
                assert(abs(a.spec_index(i as int)) == -a.spec_index(i as int));
            }
        };
        
        result.push(abs_val);
        
        // Prove that the invariant holds after the push
        assert(result.len() == i + 1);
        assert(forall|j: int| 0 <= j < i + 1 ==> result.spec_index(j) == abs(a.spec_index(j))) by {
            assert(forall|j: int| 0 <= j < i ==> result.spec_index(j) == abs(a.spec_index(j)));
            assert(result.spec_index(i as int) == abs_val);
            assert(abs_val == abs(a.spec_index(i as int)));
        };
        
        i += 1;
    }
    
    result
}

}