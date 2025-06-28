use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn CountUppercase(s: String) -> (count: int)
    ensures
        count >= 0,
        count == (set_int_range(0, s.len()).filter(|i: int| IsUpperCase(s.spec_index(*i)))).len(),
{
    let mut count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == (set_int_range(0, i).filter(|j: int| IsUpperCase(s.spec_index(*j)))).len(),
    {
        let c = s.get_char(i);
        if IsUpperCase(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}