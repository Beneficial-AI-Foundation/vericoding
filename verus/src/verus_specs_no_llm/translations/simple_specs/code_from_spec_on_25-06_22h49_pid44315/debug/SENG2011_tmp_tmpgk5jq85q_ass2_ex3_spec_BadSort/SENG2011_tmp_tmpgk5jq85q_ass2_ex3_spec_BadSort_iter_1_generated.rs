use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // all b's are before all a's && d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'b' && (s.spec_index(j) == 'a' || s.spec_index(j) == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'a' && s.spec_index(j) == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'a' && s.spec_index(j) == 'd' ==> i < j) &&
    // all d's are after all b's && a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'd' && (s.spec_index(j) == 'a' || s.spec_index(j) == 'b') ==> i > j)
}

fn BadSort(a: String) -> (b: String)
    requires
        forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    ensures
        sortedbad(b),
        multiset(a.spec_index(..)) == multiset(b.spec_index(..)),
        a.len() == b.len()
{
    let mut result = String::new();
    let mut i = 0;
    
    // First pass: add all 'b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    {
        if a.as_bytes()[i] == 'b' as u8 {
            result.push('b');
        }
        i = i + 1;
    }
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b' || result.spec_index(k) == 'a',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    {
        if a.as_bytes()[i] == 'a' as u8 {
            result.push('a');
        }
        i = i + 1;
    }
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b' || result.spec_index(k) == 'a' || result.spec_index(k) == 'd',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    {
        if a.as_bytes()[i] == 'd' as u8 {
            result.push('d');
        }
        i = i + 1;
    }
    
    result
}

}