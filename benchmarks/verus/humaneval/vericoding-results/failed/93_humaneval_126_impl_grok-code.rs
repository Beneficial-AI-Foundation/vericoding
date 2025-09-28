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
fn is_sorted_ascending_check(lst: &Vec<i8>) -> (result: bool)
    requires valid_input(lst@.map(|_i: int, x: i8| x as int))
    ensures
        result == is_sorted_ascending(lst@.map(|_i: int, x: i8| x as int))
{
    let mut i: int = 0;
    while i as usize < lst.len() - 1
        invariant
            forall|j| 0 <= j < i ==> lst@[j] <= lst@[j + 1],
            0 <= i <= lst.len() - 1 as int
    {
        if lst[i as usize] > lst[(i + 1) as usize] {
            return false;
        }
        i += 1;
    }
    return true;
}

fn no_more_than_two_duplicates_check(lst: &Vec<i8>) -> (result: bool)
    requires valid_input(lst@.map(|_i: int, x: i8| x as int))
    ensures
        result == no_more_than_two_duplicates(lst@.map(|_i: int, x: i8| x as int))
{
    if lst.len() == 0 {
        return true;
    }
    // find max
    let mut max_val = lst[0];
    let mut i: int = 1;
    while i as usize < lst.len()
        invariant
            1 <= i <= lst.len() as int,
            forall|j| 0 <= j < i ==> lst@[j] <= max_val as int,
            0 <= max_val as int
    {
        if lst[i as usize] > max_val {
            max_val = lst[i as usize];
        }
        i += 1;
    }
    let mut counts: Vec<i32> = Vec::new();
    i = 0;
    while i as usize < (max_val as usize + 1)
        invariant
            0 <= i <= max_val as usize + 1 as int,
            counts.len() as int == i,
            forall|k| 0 <= k < counts@.len() ==> counts@[k] == 0
    {
        counts.push(0);
        i += 1;
    }
    i = 0;
    while i as usize < lst.len()
        invariant
            0 <= i <= lst.len() as int,
            forall|k| 0 <= k < i ==> counts@[lst@[k]] >= 1,
            forall|k| 0 <= k < counts@.len() ==> counts@[k] >= 0
    {
        let val = lst[i as usize] as usize;
        counts[val] = counts[val] + 1;
        i += 1;
    }
    i = 0;
    while i as usize < counts.len()
        invariant
            0 <= i <= counts.len() as int,
            forall|k| 0 <= k < i ==> counts@[k] <= 2
    {
        if counts[i as usize] > 2 {
            return false;
        }
        i += 1;
    }
    return true;
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
    let is_sorted = is_sorted_ascending_check(&lst);
    let no_dup = no_more_than_two_duplicates_check(&lst);
    is_sorted && no_dup
}
// </vc-code>


}

fn main() {}