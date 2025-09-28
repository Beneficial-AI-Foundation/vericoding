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

spec fn median_value(l: Seq<int>) -> int {
    if l.len() == 0 {
        0int
    } else {
        let sorted_list = sort(l);
        let n = sorted_list.len();
        if n % 2 == 1 {
            sorted_list[(n / 2) as int]
        } else {
            (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): proof that insert_sorted preserves multiset equality */
proof fn insert_sorted_preserves_multiset(x: int, sorted: Seq<int>)
    decreases sorted.len()
    ensures
        multiset_from_seq(insert_sorted(x, sorted)) == multiset_from_seq(sorted).insert(x),
{
    if sorted.len() == 0 {
    } else {
        if x <= sorted[0] {
        } else {
            insert_sorted_preserves_multiset(x, sorted.subrange(1, sorted.len() as int));
        }
    }
}

/* helper modified by LLM (iteration 2): proof that insert_sorted preserves multiset equality */
proof fn insert_sorted_is_sorted(x: int, sorted: Seq<int>)
    requires is_sorted(sorted)
    decreases sorted.len()
    ensures is_sorted(insert_sorted(x, sorted))
{
    if sorted.len() == 0 {
    } else if x <= sorted[0] {
        let res = seq![x].add(sorted);
        assert forall|i: int, j: int| 0 <= i < j < res.len() ==> #[trigger] res[i] <= res[j];
    } else {
        let tail = sorted.subrange(1, sorted.len() as int);
        insert_sorted_is_sorted(x, tail);
        let insert_tail = insert_sorted(x, tail);
        let res = seq![sorted[0]].add(insert_tail);
        assert forall|i: int, j: int| 0 <= i < j < res.len() ==> #[trigger] res[i] <= res[j];
    }
}

/* helper modified by LLM (iteration 2): proof that insert_sorted maintains sorted order */
proof fn sort_preserves_multiset(s: Seq<int>)
    decreases s.len()
    ensures multiset_from_seq(sort(s)) == multiset_from_seq(s)
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        sort_preserves_multiset(tail);
        let sorted_tail = sort(tail);
        insert_sorted_preserves_multiset(s[0], sorted_tail);
    }
}

/* helper modified by LLM (iteration 2): proof that sort preserves multiset */
proof fn sort_is_sorted(s: Seq<int>)
    decreases s.len()
    ensures is_sorted(sort(s))
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        sort_is_sorted(tail);
        let sorted_tail = sort(tail);
        insert_sorted_is_sorted(s[0], sorted_tail);
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
    /* code modified by LLM (iteration 4): compute median by sorting and finding middle element */
    let sorted_list = sort(l);
    let n = sorted_list.len();
    if n % 2 == 1 {
        sorted_list[(n / 2) as int]
    } else {
        (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
    }
}
// </vc-code>


}

fn main() {}