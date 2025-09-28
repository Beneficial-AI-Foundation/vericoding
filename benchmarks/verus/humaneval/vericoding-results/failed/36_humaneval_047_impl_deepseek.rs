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
proof fn lemma_idx_conversion(sorted: Seq<int>, idx: nat)
    requires
        idx < sorted.len(),
    ensures
        sorted[idx as int] == sorted@[idx],
{
}

proof fn lemma_odd_case_median(l: Seq<int>)
    requires
        l.len() % 2 == 1,
        l.len() > 0,
        is_sorted(sort(l)),
    ensures
        median_value(l) == sort(l)@[l.len() / 2],
{
    reveal(median_value);
}

proof fn lemma_even_case_median(l: Seq<int>)
    requires
        l.len() % 2 == 0,
        l.len() > 0,
        is_sorted(sort(l)),
    ensures
        median_value(l) == (sort(l)@[l.len() / 2 - 1] + sort(l)@[l.len() / 2]) / 2,
{
    reveal(median_value);
}

proof fn lemma_sort_correct(l: Seq<int>)
    requires
        l.len() > 0,
    ensures
        is_sorted(sort(l)),
        multiset_from_seq(sort(l)) == multiset_from_seq(l),
{
    /* helper modified by LLM (iteration 5): Remove admit() and provide actual proof */
    if l.len() == 1 {
        assert(sort(l) =~= seq![l[0]]);
        assert(is_sorted(seq![l[0]]));
        assert(multiset_from_seq(seq![l[0]]) =~= Multiset::singleton(l[0]));
    } else {
        let tail = l.subrange(1, l.len() as int);
        lemma_sort_correct(tail);
        assert(is_sorted(sort(tail)));
        assert(multiset_from_seq(sort(tail)) == multiset_from_seq(tail));
        
        let sorted_head = insert_sorted(l[0], sort(tail));
        assert(sorted_head =~= sort(l));
        
        // Prove insertion preserves sortedness
        assert(forall|i: int, j: int| 0 <= i < j < sorted_head.len() ==> sorted_head[i] <= sorted_head[j]);
        
        // Prove insertion preserves multiset
        assert(multiset_from_seq(sorted_head) == Multiset::singleton(l[0]).add(multiset_from_seq(sort(tail))));
        assert(multiset_from_seq(sorted_head) == Multiset::singleton(l[0]).add(multiset_from_seq(tail)));
        assert(multiset_from_seq(sorted_head) == multiset_from_seq(l));
    }
}

proof fn lemma_len_one_median(l: Seq<int>)
    requires
        l.len() == 1,
    ensures
        median_value(l) == l[0],
{
    reveal(median_value);
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
    /* code modified by LLM (iteration 5): Fix casting syntax and proper variable declarations */
    let n = l.len();
    proof {
        lemma_sort_correct(l);
        let sorted_list = sort(l);
        if n == 1 {
            lemma_len_one_median(l);
        } else if n % 2 == 1 {
            lemma_odd_case_median(l);
            {
                let idx: nat = (n / 2) as nat;
                lemma_idx_conversion(sorted_list, idx);
            }
        } else {
            lemma_even_case_median(l);
            {
                let idx1: nat = (n / 2 - 1) as nat;
                let idx2: nat = (n / 2) as nat;
                lemma_idx_conversion(sorted_list, idx1);
                lemma_idx_conversion(sorted_list, idx2);
            }
        }
    }
    let sorted = sort(l);
    if n % 2 == 1 {
        sorted[(n / 2) as int]
    } else {
        (sorted[(n / 2 - 1) as int] + sorted[(n / 2) as int]) / 2
    }
}
// </vc-code>


}

fn main() {}