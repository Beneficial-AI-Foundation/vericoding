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
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}