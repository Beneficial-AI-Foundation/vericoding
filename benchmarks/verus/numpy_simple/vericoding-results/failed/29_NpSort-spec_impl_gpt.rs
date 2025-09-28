// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix nat literal types in multiset count equalities */
spec fn is_sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() as int ==> (s[i] as int) <= (s[j] as int)
}

spec fn insert_sorted(s: Seq<i8>, x: i8) -> Seq<i8>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::<i8>::empty().push(x)
    } else {
        let h = s[0];
        let t = s.subrange(1, s.len() as int);
        if (x as int) <= (h as int) {
            Seq::<i8>::empty().push(x) + s
        } else {
            Seq::<i8>::empty().push(h) + insert_sorted(t, x)
        }
    }
}

proof fn lemma_insert_sorted_props(s: Seq<i8>, x: i8)
    requires
        is_sorted(s),
    ensures
        is_sorted(insert_sorted(s, x)),
        forall|y: i8| multiset_count(insert_sorted(s, x), y) == multiset_count(s, y) + (if y == x { 1nat } else { 0nat }),
        insert_sorted(s, x).len() == s.len() + 1,
    decreases s.len()
{
    if s.len() == 0 {
        assert(insert_sorted(s, x).len() == 1);
        assert(forall|y: i8| multiset_count(insert_sorted(s, x), y) == if y == x { 1nat } else { 0nat });
        assert(is_sorted(insert_sorted(s, x)));
    } else {
        let h = s[0];
        let t = s.subrange(1, s.len() as int);
        // Tail is sorted
        assert(is_sorted(t)) by {
            assert(forall|i: int, j: int| 0 <= i < j < t.len() as int ==> (t[i] as int) <= (t[j] as int)) by {
                assert(forall|i: int, j: int| 0 <= i + 1 < j + 1 < s.len() as int ==> (s[i + 1] as int) <= (s[j + 1] as int));
            };
        };
        if (x as int) <= (h as int) {
            // Show x <= every element of s
            assert(forall|j: int| 0 <= j < s.len() as int ==> (h as int) <= (s[j] as int)) by {
                assert(s.len() > 0);
                assert(forall|j: int| 1 <= j < s.len() as int ==> (s[0] as int) <= (s[j] as int));
            };
            assert(is_sorted(insert_sorted(s, x))) by {
                assert(forall|j: int| 0 <= j < s.len() as int ==> (x as int) <= (s[j] as int));
            };
            assert(insert_sorted(s, x).len() == s.len() + 1);
        } else {
            // Recursive step on tail
            lemma_insert_sorted_props(t, x);
            // h <= all elements of t
            assert(forall|j: int| 0 <= j < t.len() as int ==> (h as int) <= (t[j] as int)) by {
                assert(forall|j: int| 1 <= j + 1 < s.len() as int ==> (s[0] as int) <= (s[j + 1] as int));
            };
            assert((h as int) <= (x as int));
            assert(is_sorted(insert_sorted(s, x))) by {
                assert(is_sorted(insert_sorted(t, x)));
                assert(forall|j: int| 0 <= j < insert_sorted(t, x).len() as int ==> (h as int) <= (insert_sorted(t, x)[j] as int));
            };
            assert(insert_sorted(s, x).len() == s.len() + 1);
        }
        assert(forall|y: i8| multiset_count(insert_sorted(s, x), y) == multiset_count(s, y) + (if y == x { 1nat } else { 0nat }));
    }
}

spec fn sort_seq(s: Seq<i8>) -> Seq<i8>
    decreases s.len()
{
    if s.len() == 0 { s } else { insert_sorted(sort_seq(s.take(s.len() - 1)), s[(s.len() - 1) as int]) }
}

proof fn lemma_sort_seq_props(s: Seq<i8>)
    ensures
        is_sorted(sort_seq(s)),
        forall|y: i8| multiset_count(sort_seq(s), y) == multiset_count(s, y),
        sort_seq(s).len() == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
        assert(sort_seq(s).len() == 0);
        assert(forall|y: i8| multiset_count(sort_seq(s), y) == multiset_count(s, y));
        assert(is_sorted(sort_seq(s)));
    } else {
        let n = s.len();
        let pref = s.take(n - 1);
        let last = s[(n - 1) as int];
        lemma_sort_seq_props(pref);
        lemma_insert_sorted_props(sort_seq(pref), last);
        assert(sort_seq(s).len() == sort_seq(pref).len() + 1);
        assert(sort_seq(s).len() == s.len());
        assert(is_sorted(sort_seq(s)));
        assert(forall|y: i8| multiset_count(sort_seq(s), y) == multiset_count(s, y));
    }
}
// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use Vec::from to convert the sorted spec Seq into a Vec and discharge specs */
    proof { lemma_sort_seq_props(a@); }
    let s = sort_seq(a@);
    let result = Vec::<i8>::from(s);
    proof { assert(result@ == s); }
    result
}
// </vc-code>


}
fn main() {}