use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinSecondValueFirst(s: Vec<Seq<int>>) -> (firstOfMinSecond: int)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s.spec_index(i).len() >= 2
    ensures
        exists|i: int| 0 <= i < s.len() && firstOfMinSecond == s.spec_index(i)[0] && 
        (forall|j: int| 0 <= j < s.len() ==> s.spec_index(i)[1] <= s.spec_index(j)[1])
{
    let mut min_second_value = s[0][1];
    let mut result_first = s[0][0];
    let mut min_index = 0;
    
    for i in 1..s.len()
        invariant
            0 <= min_index < s.len(),
            min_second_value == s.spec_index(min_index as int)[1],
            result_first == s.spec_index(min_index as int)[0],
            forall|j: int| 0 <= j < i ==> min_second_value <= s.spec_index(j)[1],
            min_index < i,
    {
        if s[i][1] < min_second_value {
            min_second_value = s[i][1];
            result_first = s[i][0];
            min_index = i;
        }
    }
    
    // After the loop, we have checked all elements from 0 to s.len()-1
    // The loop invariant gives us: forall|j: int| 0 <= j < s.len() ==> min_second_value <= s.spec_index(j)[1]
    // because i reaches s.len() at the end of the loop
    
    assert(forall|j: int| 0 <= j < s.len() ==> min_second_value <= s.spec_index(j)[1]);
    assert(0 <= min_index < s.len());
    assert(result_first == s.spec_index(min_index as int)[0]);
    assert(min_second_value == s.spec_index(min_index as int)[1]);
    
    // This directly satisfies the postcondition with min_index as the witness
    result_first
}

}