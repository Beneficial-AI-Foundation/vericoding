use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn CountDigits(s: String) -> (count: int)
    ensures
        count >= 0,
        count == (Set::<int>::new(|i: int| 0 <= i < s.len() && IsDigit(s.spec_index(i)))).len(),
{
    let mut count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == (Set::<int>::new(|j: int| 0 <= j < i && IsDigit(s.spec_index(j)))).len(),
    {
        if IsDigit(s.spec_index(i)) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}