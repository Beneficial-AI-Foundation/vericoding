use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) + 32
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn ToLowercase(s: String) -> (v: String)
    requires
        // Ensure string contains only ASCII characters for simplicity
        forall|i: int| 0 <= i < s.len() ==> 0 <= s.spec_index(i) as int <= 127
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsUpperCase(s.spec_index(i)) then 
                IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) 
            else 
                v.spec_index(i) == s.spec_index(i)
{
    let mut result: String = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            result.len() == i,
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> 0 <= result.spec_index(j) as int <= 127,
            forall|j: int| 0 <= j < i ==> 
                if IsUpperCase(s.spec_index(j)) then 
                    IsUpperLowerPair(s.spec_index(j), result.spec_index(j))
                else 
                    result.spec_index(j) == s.spec_index(j)
    {
        let c = s.spec_index(i as int);
        
        if IsUpperCase(c) {
            // Convert to lowercase by adding 32
            let lower_c = ((c as u8) + 32) as char;
            result.push(lower_c);
            
            // Proof that the conversion is correct
            assert((c as int) == (lower_c as int) + 32);
            assert(IsUpperLowerPair(c, lower_c));
        } else {
            result.push(c);
            assert(result.spec_index(i as int) == s.spec_index(i as int));
        }
        
        i += 1;
    }
    
    result
}

}