use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsZ(s: &str) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))
{
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z'),
    {
        let c = s.chars().nth(i).unwrap();
        if c == 'z' || c == 'Z' {
            assert(exists|k: int| 0 <= k < s.len() && (s.spec_index(k) == 'z' || s.spec_index(k) == 'Z')) by {
                assert(0 <= i < s.len());
                assert(c == 'z' || c == 'Z');
                assert(s.spec_index(i as int) == c);
            };
            return true;
        }
        assert(!(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z')) by {
            assert(s.spec_index(i as int) == c);
            assert(c != 'z' && c != 'Z');
        };
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z'));
    assert(!(exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))) by {
        if exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z') {
            let witness_i = choose|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z');
            assert(0 <= witness_i < s.len());
            assert(!(s.spec_index(witness_i) == 'z' || s.spec_index(witness_i) == 'Z'));
            assert(false);
        }
    };
    
    false
}

}