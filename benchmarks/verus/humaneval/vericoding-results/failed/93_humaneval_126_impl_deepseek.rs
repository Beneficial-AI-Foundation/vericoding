// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < lst.len() ==> lst[i] >= 0
}

spec fn is_sorted_ascending(lst: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] <= lst[j]
}

spec fn no_more_than_two_duplicates(lst: Seq<int>) -> bool {
    forall|i: int| #![auto] 0 <= i < lst.len() ==> count_occurrences(lst, lst[i]) <= 2
}

spec fn valid_list(lst: Seq<int>) -> bool {
    valid_input(lst) && is_sorted_ascending(lst) && no_more_than_two_duplicates(lst)
}
spec fn count_occurrences(lst: Seq<int>, value: int) -> int
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else if lst[0] == value {
        1 + count_occurrences(lst.drop_first(), value)
    } else {
        count_occurrences(lst.drop_first(), value)
    }
}

spec fn has_more_than_two_occurrences(lst: Seq<int>, index: int) -> bool
    decreases lst.len() - index when 0 <= index <= lst.len()
{
    if index == lst.len() {
        false
    } else if 0 <= index < lst.len() && count_occurrences(lst, lst[index]) > 2 {
        true
    } else if 0 <= index < lst.len() {
        has_more_than_two_occurrences(lst, index + 1)
    } else {
        false
    }
}

spec fn is_sorted_ascending_from_index(lst: Seq<int>, index: int) -> bool
    decreases lst.len() - index when 0 <= index <= lst.len()
{
    if index >= lst.len() - 1 {
        true
    } else if 0 <= index < lst.len() - 1 && lst[index] > lst[index + 1] {
        false
    } else if 0 <= index < lst.len() {
        is_sorted_ascending_from_index(lst, index + 1)
    } else {
        true
    }
}

spec fn is_sorted(lst: Seq<int>) -> bool {
    if lst.len() <= 1 {
        true
    } else if !is_sorted_ascending_from_index(lst, 0) {
        false
    } else {
        !has_more_than_two_occurrences(lst, 0)
    }
}

// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_occurrences_nonnegative(lst: Seq<int>, value: int)
    decreases lst.len()
    ensures count_occurrences(lst, value) >= 0
{
    if lst.len() == 0 {
    } else {
        lemma_count_occurrences_nonnegative(lst.drop_first(), value);
    }
}

proof fn lemma_sorted_implies_ascending_from_index(lst: Seq<int>)
    ensures is_sorted_ascending(lst) == is_sorted_ascending_from_index(lst, 0)
{
    reveal(is_sorted_ascending);
    reveal(is_sorted_ascending_from_index);
}

proof fn lemma_no_more_than_two_eq_has_more_than_two_occurrences(lst: Seq<int>)
    ensures no_more_than_two_duplicates(lst) == !has_more_than_two_occurrences(lst, 0)
{
    reveal(no_more_than_two_duplicates);
    reveal(has_more_than_two_occurrences);
}

proof fn lemma_is_sorted_correct(lst: Seq<int>)
    ensures is_sorted(lst) == (valid_input(lst) && is_sorted_ascending(lst) && no_more_than_two_duplicates(lst))
{
    reveal(is_sorted);
    reveal(valid_input);
    reveal(is_sorted_ascending);
    reveal(no_more_than_two_duplicates);
    
    if lst.len() <= 1 {
        assert(is_sorted(lst));
    } else if !is_sorted_ascending_from_index(lst, 0) {
        lemma_sorted_implies_ascending_from_index(lst);
    } else {
        lemma_no_more_than_two_eq_has_more_than_two_occurrences(lst);
    }
}
// </vc-helpers>

// <vc-spec>
fn check_valid_list(lst: Vec<i8>) -> (result: bool)
    requires 
        valid_input(lst@.map(|_i: int, x: i8| x as int))
    ensures 
        result == valid_list(lst@.map(|_i: int, x: i8| x as int)),
        result == (is_sorted_ascending(lst@.map(|_i: int, x: i8| x as int)) && no_more_than_two_duplicates(lst@.map(|_i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ensures clause syntax with proper braces */
    proof {
        lemma_is_sorted_correct(lst@.map(|_i: int, x: i8| x as int));
    }
    let sorted = is_sorted_ascending(lst@.map(|_i: int, x: i8| x as int));
    let no_duplicates = no_more_than_two_duplicates(lst@.map(|_i: int, x: i8| x as int));
    sorted && no_duplicates
}
// </vc-code>


}

fn main() {}