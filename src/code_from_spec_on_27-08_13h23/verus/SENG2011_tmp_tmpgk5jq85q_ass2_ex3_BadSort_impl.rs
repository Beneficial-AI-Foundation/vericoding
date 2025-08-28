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
spec fn count_chars(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

proof fn multiset_preservation(a: Seq<char>, b: Seq<char>)
    requires
        a.to_multiset() =~= b.to_multiset(),
        a.len() == b.len(),
    ensures
        count_chars(a, 'b') == count_chars(b, 'b'),
        count_chars(a, 'a') == count_chars(b, 'a'),
        count_chars(a, 'd') == count_chars(b, 'd'),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bad_sort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
    ensures
        sortedbad(b@),
        a@.to_multiset() =~= b@.to_multiset(),
        a.len() == b.len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bad_sort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
    ensures
        sortedbad(b@),
        a@.to_multiset() =~= b@.to_multiset(),
        a.len() == b.len(),
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let len = a.len();

    // Count the number of each character
    let mut count_b: usize = 0;
    let mut count_a: usize = 0;
    let mut count_d: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            count_b == count_chars(a@.subrange(0, i as int), 'b'),
            count_a == count_chars(a@.subrange(0, i as int), 'a'),
            count_d == count_chars(a@.subrange(0, i as int), 'd'),
    {
        if a[i] == 'b' {
            count_b = count_b + 1;
        } else if a[i] == 'a' {
            count_a = count_a + 1;
        } else {
            count_d = count_d + 1;
        }
        i = i + 1;
    }

    // Push all 'b's
    i = 0;
    while i < count_b
        invariant
            0 <= i <= count_b,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == 'b',
    {
        result.push('b');
        i = i + 1;
    }

    // Push all 'a's
    i = 0;
    while i < count_a
        invariant
            0 <= i <= count_a,
            result.len() == count_b + i,
            forall|k: int| 0 <= k < count_b ==> result@[k] == 'b',
            forall|k: int| count_b <= k < count_b + i ==> result@[k] == 'a',
    {
        result.push('a');
        i = i + 1;
    }

    // Push all 'd's
    i = 0;
    while i < count_d
        invariant
            0 <= i <= count_d,
            result.len() == count_b + count_a + i,
            forall|k: int| 0 <= k < count_b ==> result@[k] == 'b',
            forall|k: int| count_b <= k < count_b + count_a ==> result@[k] == 'a',
            forall|k: int| count_b + count_a <= k < count_b + count_a + i ==> result@[k] == 'd',
    {
        result.push('d');
        i = i + 1;
    }

    proof {
        multiset_preservation(a@, result@);
    }

    result
}
// </vc-code>

fn main() {}

}