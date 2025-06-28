use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i - n + l.len()) % l.len())
{
    if l.len() == 0 {
        return l;
    }
    
    let effective_n = n % (l.len() as int);
    let split_point = (l.len() - effective_n) % (l.len() as int);
    
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, l.len() as int);
    
    let result = right_part + left_part;
    
    // Proof annotations to help verification
    assert(result.len() == right_part.len() + left_part.len());
    assert(right_part.len() == l.len() - split_point);
    assert(left_part.len() == split_point);
    assert(result.len() == l.len());
    
    // Help prove the main postcondition
    assert forall|i: int| 0 <= i < result.len() implies {
        let original_index = (i - n + l.len()) % l.len();
        result.spec_index(i) == l.spec_index(original_index)
    } by {
        if 0 <= i < result.len() {
            let original_index = (i - n + l.len()) % l.len();
            if i < right_part.len() {
                // i is in the right part
                assert(result.spec_index(i) == right_part.spec_index(i));
                assert(right_part.spec_index(i) == l.spec_index(split_point + i));
                // Need to show that split_point + i == original_index
                assert((split_point + i - n + l.len()) % l.len() == split_point + i);
            } else {
                // i is in the left part
                let left_index = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_index));
                assert(left_part.spec_index(left_index) == l.spec_index(left_index));
                // Need to show that left_index == original_index
            }
        }
    };
    
    result
}

}