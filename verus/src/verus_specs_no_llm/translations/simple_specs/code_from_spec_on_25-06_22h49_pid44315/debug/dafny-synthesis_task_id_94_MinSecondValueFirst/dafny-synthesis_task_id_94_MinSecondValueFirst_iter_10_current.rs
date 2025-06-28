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
    
    // After the loop, we need to prove that min_index gives us the global minimum
    // The invariant tells us that min_second_value is <= all elements in [0, s.len())
    // because the loop covered [1, s.len()) and we initialized with s[0]
    
    assert(0 <= min_index < s.len());
    assert(result_first == s.spec_index(min_index as int)[0]);
    assert(min_second_value == s.spec_index(min_index as int)[1]);
    
    // We need to prove that min_second_value <= s.spec_index(j)[1] for all j in [0, s.len())
    assert(forall|j: int| 0 <= j < s.len() ==> {
        if j == 0 {
            min_second_value <= s.spec_index(j)[1]  // true because we checked all elements
        } else {
            min_second_value <= s.spec_index(j)[1]  // true from loop invariant
        }
    });
    
    result_first
}

}