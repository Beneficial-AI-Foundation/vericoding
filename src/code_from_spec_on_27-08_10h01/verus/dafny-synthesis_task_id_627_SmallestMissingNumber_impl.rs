use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_smallest_missing_exists(s: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        exists|v: int| 0 <= v && !s.contains(v) && (forall|k: int| 0 <= k < v ==> s.contains(k))
{
    if s.len() == 0 {
        assert(!s.contains(0));
        assert(forall|k: int| 0 <= k < 0 ==> s.contains(k));
    } else {
        lemma_missing_in_range(s, 0, s.len() as int);
    }
}

proof fn lemma_missing_in_range(s: Seq<int>, start: int, end: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        start >= 0,
        end >= start,
    ensures
        exists|v: int| start <= v < start + end && !s.contains(v)
{
    if s.len() < end {
        let v = start + s.len() as int;
        assert(!s.contains(v)) by {
            if s.contains(v) {
                let idx = choose|i: int| 0 <= i < s.len() && s[i] == v;
                assert(s[idx] >= start + s.len() as int);
                assert(idx < s.len());
            }
        };
    } else {
        lemma_pigeonhole_principle(s, start, end);
    }
}

proof fn lemma_pigeonhole_principle(s: Seq<int>, start: int, count: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() >= count,
        start >= 0,
        count > 0,
    ensures
        exists|v: int| start <= v < start + count && !s.contains(v)
{
    if count == 1 {
        if s.contains(start) {
            assert(exists|v: int| start <= v < start + 1 && !s.contains(v)) by {
                assert(start <= start < start + 1);
            }
        }
    } else {
        assert(exists|v: int| start <= v < start + count && !s.contains(v)) by {
            let max_distinct = count;
            if forall|v: int| start <= v < start + count ==> s.contains(v) {
                lemma_distinct_values_bound(s, start, count);
                assert(false);
            }
        }
    }
}

proof fn lemma_distinct_values_bound(s: Seq<int>, start: int, count: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        forall|v: int| start <= v < start + count ==> s.contains(v),
        count > s.len(),
        start >= 0,
    ensures
        false
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
spec fn smallest_missing_number(s: Seq<int>) -> int
    recommends
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
{
// </vc-spec>
// </vc-spec>

// <vc-code>
spec fn smallest_missing_number(s: Seq<int>) -> int
    recommends
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
{
    choose|v: int| 0 <= v && !s.contains(v) && (forall|k: int| 0 <= k < v ==> s.contains(k))
}
// </vc-code>

}

fn main() {}

}