use vstd::prelude::*;

verus! {

// verifies
// all bs are before all as which are before all ds

spec fn sortedbad(s: Seq<char>) -> bool {
    // all b's are before all a's and d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'd' ==> i < j) &&
    // all d's are after all b's and a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}

// <vc-helpers>
spec fn count_char(s: Seq<char>, c: char) -> int {
    if s.is_empty() {
        0
    } else if s.last() == c {
        1 + count_char(s.drop_last(), c)
    } else {
        count_char(s.drop_last(), c)
    }
}
// </vc-helpers>

// <vc-spec>
fn bad_sort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
    ensures
        sortedbad(b@),
        a@.to_multiset() =~= b@.to_multiset(),
        a.len() == b.len(),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut count_b: usize = 0;
    let mut count_a: usize = 0;
    let mut count_d: usize = 0;
    let mut i: usize = 0;
    
    // Counting loop
    while i < a.len()
        invariant
            0 <= i as int <= a@.len(),
            count_b as int == count_char(a@.subrange(0, i as int), 'b'),
            count_a as int == count_char(a@.subrange(0, i as int), 'a'),
            count_d as int == count_char(a@.subrange(0, i as int), 'd'),
            forall |k: int| 0 <= k < i as int ==> a@[k] == 'b' || a@[k] == 'a' || a@[k] == 'd',
        decreases a@.len() - i as int,
    {
        if a[i] == 'b' {
            count_b += 1;
        } else if a[i] == 'a' {
            count_a += 1;
        } else {
            // Must be 'd' per requires
            count_d += 1;
        }
        i += 1;
    }
    
    // Build the result vector: b's first
    let mut j: usize = 0;
    while j < count_b
        invariant
            0 <= j as int <= count_b as int,
            result@.len() == j as int,
            forall |k: int| 0 <= k < result@.len() ==> result@[k] == 'b',
        decreases count_b as int - j as int,
    {
        result.push('b');
        j += 1;
    }
    
    // Then a's
    j = 0;
    while j < count_a
        invariant
            0 <= j as int <= count_a as int,
            result@.len() == count_b as int + j as int,
            forall |k: int| 0 <= k < count_b as int ==> result@[k] == 'b',
            forall |k: int| count_b as int <= k < count_b as int + j as int ==> result@[k] == 'a',
        decreases count_a as int - j as int,
    {
        result.push('a');
        j += 1;
    }
    
    // Then d's
    j = 0;
    while j < count_d
        invariant
            0 <= j as int <= count_d as int,
            result@.len() == count_b as int + count_a as int + j as int,
            forall |k: int| 0 <= k < count_b as int ==> result@[k] == 'b',
            forall |k: int| count_b as int <= k < count_b as int + count_a as int ==> result@[k] == 'a',
            forall |k: int| count_b as int + count_a as int <= k < count_b as int + count_a as int + j as int ==> result@[k] == 'd',
        decreases count_d as int - j as int,
    {
        result.push('d');
        j += 1;
    }
    
    proof {
        assert(count_char(result@, 'b') == count_b as int);
        assert(count_char(result@, 'a') == count_a as int);
        assert(count_char(result@, 'd') == count_d as int);
        assert(count_char(a@, 'b') == count_b as int);
        assert(count_char(a@, 'a') == count_a as int);
        assert(count_char(a@, 'd') == count_d as int);
        assert(count_char(result@, 'b') == count_char(a@, 'b'));
        assert(count_char(result@, 'a') == count_char(a@, 'a'));
        assert(count_char(result@, 'd') == count_char(a@, 'd'));
        assert(a@.to_multiset() =~= result@.to_multiset());
        assert(result@.len() == a@.len());
        // Multiset equality follows from equal character counts
        // sortedbad holds by construction
    }
    
    result
}
// </vc-code>

fn main() {}

}