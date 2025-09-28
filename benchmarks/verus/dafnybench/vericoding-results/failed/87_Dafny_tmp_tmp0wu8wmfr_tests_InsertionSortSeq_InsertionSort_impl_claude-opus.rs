use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn insert_sorted(s: Seq<int>, x: int) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![x]
    } else if x <= s[0] {
        seq![x] + s
    } else {
        seq![s[0]] + insert_sorted(s.subrange(1, s.len() as int), x)
    }
}

fn insert_sorted_exec(s: Vec<int>, x: int) -> (result: Vec<int>)
    requires is_sorted(s@),
    ensures 
        result@ == insert_sorted(s@, x),
        result@.to_multiset() == s@.to_multiset().insert(x),
        is_sorted(result@),
    decreases s.len(),
{
    proof {
        insert_sorted_maintains_multiset(s@, x);
    }
    
    if s.len() == 0 {
        vec![x]
    } else if x <= s[0] {
        let mut result = Vec::new();
        result.push(x);
        let mut i = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result@ == seq![x] + s@.subrange(0, i as int),
        {
            result.push(s[i]);
            i += 1;
        }
        result
    } else {
        let mut tail = Vec::new();
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                tail@ == s@.subrange(1, i as int),
        {
            tail.push(s[i]);
            i += 1;
        }
        assert(tail@ == s@.subrange(1, s.len() as int));
        
        let inserted = insert_sorted_exec(tail, x);
        let mut result = Vec::new();
        result.push(s[0]);
        let mut j = 0;
        while j < inserted.len()
            invariant
                0 <= j <= inserted.len(),
                result@ == seq![s[0]] + inserted@.subrange(0, j as int),
        {
            result.push(inserted[j]);
            j += 1;
        }
        assert(result@ == seq![s[0]] + inserted@);
        result
    }
}

proof fn insert_sorted_maintains_multiset(s: Seq<int>, x: int)
    requires is_sorted(s),
    ensures 
        insert_sorted(s, x).to_multiset() == s.to_multiset().insert(x),
        is_sorted(insert_sorted(s, x)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(insert_sorted(s, x) == seq![x]);
    } else if x <= s[0] {
        assert(insert_sorted(s, x) == seq![x] + s);
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(is_sorted(tail)) by {
            assert forall|p: int, q: int| 0 <= p < q < tail.len() implies #[trigger] tail[p] <= #[trigger] tail[q] by {
                assert(tail[p] == s[p + 1]);
                assert(tail[q] == s[q + 1]);
            }
        }
        insert_sorted_maintains_multiset(tail, x);
        let result = seq![s[0]] + insert_sorted(tail, x);
        assert(result == insert_sorted(s, x));
        
        assert(is_sorted(result)) by {
            assert forall|p: int, q: int| 0 <= p < q < result.len() implies #[trigger] result[p] <= #[trigger] result[q] by {
                if p == 0 {
                    assert(result[0] == s[0]);
                    if q == 1 {
                        if x <= s[0] {
                            assert(false);
                        } else {
                            let inserted = insert_sorted(tail, x);
                            assert(result[1] == inserted[0]);
                            if tail.len() == 0 {
                                assert(inserted == seq![x]);
                                assert(result[1] == x);
                                assert(s[0] < x);
                            } else if x <= tail[0] {
                                assert(inserted == seq![x] + tail);
                                assert(result[1] == x);
                                assert(s[0] < x);
                            } else {
                                assert(result[1] == tail[0]);
                                assert(tail[0] == s[1]);
                            }
                        }
                    } else {
                        let inserted = insert_sorted(tail, x);
                        assert(result[q] == inserted[q - 1]);
                        assert(result[0] <= result[1]);
                        assert(result[1] <= result[q]);
                    }
                } else {
                    let inserted = insert_sorted(tail, x);
                    assert(result[p] == inserted[p - 1]);
                    assert(result[q] == inserted[q - 1]);
                    assert(inserted[p - 1] <= inserted[q - 1]);
                }
            }
        }
    }
}

spec fn insertion_sort_spec(s: Seq<int>) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::<int>::empty()
    } else {
        insert_sorted(insertion_sort_spec(s.subrange(0, (s.len() - 1) as int)), s[s.len() - 1])
    }
}

proof fn insertion_sort_spec_correct(s: Seq<int>)
    ensures 
        insertion_sort_spec(s).to_multiset() == s.to_multiset(),
        is_sorted(insertion_sort_spec(s)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(insertion_sort_spec(s) == Seq::<int>::empty());
    } else {
        let prefix = s.subrange(0, (s.len() - 1) as int);
        insertion_sort_spec_correct(prefix);
        insert_sorted_maintains_multiset(insertion_sort_spec(prefix), s[s.len() - 1]);
        
        assert(s.to_multiset() == prefix.to_multiset().insert(s[s.len() - 1])) by {
            assert(s == prefix + seq![s[s.len() - 1]]);
        }
    }
}

fn insertion_sort_exec(v: Vec<int>) -> (result: Vec<int>)
    ensures 
        result@ == insertion_sort_spec(v@),
        result@.to_multiset() == v@.to_multiset(),
        is_sorted(result@),
    decreases v.len(),
{
    if v.len() == 0 {
        Vec::new()
    } else {
        let mut prefix = Vec::new();
        let mut i = 0;
        while i < v.len() - 1
            invariant
                0 <= i <= v.len() - 1,
                prefix@ == v@.subrange(0, i as int),
        {
            prefix.push(v[i]);
            i += 1;
        }
        assert(prefix@ == v@.subrange(0, (v.len() - 1) as int));
        
        let sorted_prefix = insertion_sort_exec(prefix);
        insert_sorted_exec(sorted_prefix, v[v.len() - 1])
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
    proof {
        insertion_sort_spec_correct(s);
    }
    
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == s.subrange(0, i as int),
    {
        v.push(s[i as int]);
        i += 1;
    }
    assert(v@ == s);
    
    let result = insertion_sort_exec(v);
    result@
}
// </vc-code>

fn main() {}

}