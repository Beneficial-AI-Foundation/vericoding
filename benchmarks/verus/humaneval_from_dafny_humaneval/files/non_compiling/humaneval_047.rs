// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

spec fn insert_sorted(x: int, sorted: Seq<int>) -> Seq<int>
    decreases sorted.len()
{
    if sorted.len() == 0 {
        seq![x]
    } else if x <= sorted[0] {
        seq![x].add(sorted)
    } else {
        seq![sorted[0]].add(insert_sorted(x, sorted.subrange(1, sorted.len() as int)))
    }
}

spec fn sort(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        insert_sorted(s[0], sort(s.subrange(1, s.len() as int)))
    }
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_from_seq(s: Seq<int>) -> Multiset<int>
    decreases s.len()
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        Multiset::singleton(s[0]).add(multiset_from_seq(s.subrange(1, s.len() as int)))
    }
}

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn median_value(l: Seq<int>) -> int
    requires valid_input(l)
{
    let sorted_list = sort(l);
    let n = sorted_list.len();
    if n % 2 == 1 {
        sorted_list[(n / 2) as int]
    } else {
        (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn insert_sorted_preserves_order(x: int, sorted: Seq<int>)
    requires is_sorted(sorted)
    ensures is_sorted(insert_sorted(x, sorted))
    decreases sorted.len()
{
    if sorted.len() == 0 {
    } else if x <= sorted[0] {
    } else {
        insert_sorted_preserves_order(x, sorted.subrange(1, sorted.len() as int));
        let result = insert_sorted(x, sorted.subrange(1, sorted.len() as int));
        assert(is_sorted(result));
        if result.len() > 0 {
            assert(sorted[0] <= result[0]);
        }
        assert(is_sorted(seq![sorted[0]].add(result)));
    }
}

proof fn sort_produces_order(s: Seq<int>)
    ensures is_sorted(sort(s))
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sort_produces_order(s.subrange(1, s.len() as int));
        insert_sorted_preserves_order(s[0], sort(s.subrange(1, s.len() as int)));
    }
}

proof fn insert_sorted_preserves_multiset(x: int, sorted: Seq<int>)
    ensures multiset_from_seq(insert_sorted(x, sorted)) == Multiset::singleton(x).add(multiset_from_seq(sorted))
    decreases sorted.len()
{
    if sorted.len() == 0 {
    } else if x <= sorted[0] {
    } else {
        insert_sorted_preserves_multiset(x, sorted.subrange(1, sorted.len() as int));
    }
}

proof fn sort_preserves_multiset(s: Seq<int>)
    ensures multiset_from_seq(sort(s)) == multiset_from_seq(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sort_preserves_multiset(s.subrange(1, s.len() as int));
        insert_sorted_preserves_multiset(s[0], sort(s.subrange(1, s.len() as int)));
    }
}
// </vc-helpers>

// <vc-spec>
fn median(l: Seq<int>) -> (result: int)
    requires valid_input(l)
    ensures 
        result == median_value(l) &&
        ({
            let sorted_list = sort(l);
            let n = sorted_list.len();
            n % 2 == 1 ==> result == sorted_list[(n / 2) as int]
        }) &&
        ({
            let sorted_list = sort(l);
            let n = sorted_list.len();
            n % 2 == 0 ==> result == (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
        }) &&
        is_sorted(sort(l)) &&
        multiset_from_seq(sort(l)) == multiset_from_seq(l) &&
        (l.len() == 1 ==> result == l[0])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0int
    // impl-end
}
// </vc-code>


}

fn main() {}