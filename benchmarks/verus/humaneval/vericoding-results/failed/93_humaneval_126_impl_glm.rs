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
/* helper modified by LLM (iteration 2): changed to exec functions that work on Vec<i8> */
fn check_valid_input_exec(lst: &Vec<i8>) -> bool {
    for i in 0..lst.len() {
        if lst[i] < 0 {
            return false;
        }
    }
    true
}

fn check_sorted_ascending_exec(lst: &Vec<i8>) -> bool {
    for i in 0..lst.len() {
        if i >= 1 {
            if lst[i-1] > lst[i] {
                return false;
            }
        }
    }
    true
}

fn count_occurrences_exec(lst: &Vec<i8>, value: i8) -> usize {
    let mut count = 0;
    for i in 0..lst.len() {
        if lst[i] == value {
            count += 1;
        }
    }
    count
}

fn check_no_more_than_two_duplicates_exec(lst: &Vec<i8>) -> bool {
    for i in 0..lst.len() {
        if count_occurrences_exec(lst, lst[i]) > 2 {
            return false;
        }
    }
    true
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
/* code modified by LLM (iteration 2): replaced with exec functions that avoid int in non-ghost code */
{
    let valid_input = check_valid_input_exec(&lst);
    let is_sorted = check_sorted_ascending_exec(&lst);
    let no_duplicates = check_no_more_than_two_duplicates_exec(&lst);
    valid_input && is_sorted && no_duplicates
}
// </vc-code>


}

fn main() {}