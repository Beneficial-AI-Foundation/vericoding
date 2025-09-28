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
proof fn count_occurrences_non_negative(lst: Seq<int>, value: int)
    ensures count_occurrences(lst, value) >= 0
    decreases lst.len()
{
    if lst.len() == 0 {
    } else {
        count_occurrences_non_negative(lst.drop_first(), value);
    }
}

proof fn count_occurrences_drop_first_relation(lst: Seq<int>, value: int)
    requires lst.len() > 0
    ensures 
        lst[0] == value ==> count_occurrences(lst, value) == 1 + count_occurrences(lst.drop_first(), value),
        lst[0] != value ==> count_occurrences(lst, value) == count_occurrences(lst.drop_first(), value)
    decreases lst.len()
{
}

proof fn sorted_from_index_implies_sorted(lst: Seq<int>)
    requires is_sorted_ascending_from_index(lst, 0)
    ensures is_sorted_ascending(lst)
    decreases lst.len()
{
    if lst.len() <= 1 {
    } else {
        assert(forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] <= lst[j]) by {
            sorted_from_index_transitive(lst, 0);
        }
    }
}

proof fn sorted_from_index_transitive(lst: Seq<int>, start: int)
    requires 
        0 <= start <= lst.len(),
        is_sorted_ascending_from_index(lst, start)
    ensures 
        forall|i: int, j: int| start <= i < j < lst.len() ==> lst[i] <= lst[j]
    decreases lst.len() - start
{
    if start >= lst.len() - 1 {
    } else {
        sorted_from_index_transitive(lst, start + 1);
    }
}

proof fn no_more_than_two_equivalent(lst: Seq<int>)
    requires !has_more_than_two_occurrences(lst, 0)
    ensures no_more_than_two_duplicates(lst)
    decreases lst.len()
{
    assert(forall|i: int| 0 <= i < lst.len() ==> count_occurrences(lst, lst[i]) <= 2) by {
        no_more_than_two_helper(lst, 0);
    }
}

proof fn no_more_than_two_helper(lst: Seq<int>, index: int)
    requires 
        0 <= index <= lst.len(),
        !has_more_than_two_occurrences(lst, index)
    ensures 
        forall|i: int| index <= i < lst.len() ==> count_occurrences(lst, lst[i]) <= 2
    decreases lst.len() - index
{
    if index == lst.len() {
    } else {
        no_more_than_two_helper(lst, index + 1);
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
    /* code modified by LLM (iteration 5): use ghost variable for mapped sequence */
    ghost let mapped_seq = lst@.map(|_i: int, x: i8| x as int);
    
    // Check if sorted ascending
    let mut i = 0;
    let mut is_ascending = true;
    
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len(),
            lst.len() == mapped_seq.len(),
            mapped_seq == lst@.map(|_i: int, x: i8| x as int),
            is_ascending == is_sorted_ascending_from_index(mapped_seq, i as int),
            is_ascending ==> forall|j: int, k: int| 0 <= j < k < i ==> mapped_seq[j] <= mapped_seq[k]
    {
        if lst[i] > lst[i + 1] {
            is_ascending = false;
            break;
        }
        i += 1;
    }
    
    if !is_ascending {
        return false;
    }
    
    // Check for no more than two duplicates
    i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            lst.len() == mapped_seq.len(),
            mapped_seq == lst@.map(|_i: int, x: i8| x as int),
            is_ascending == is_sorted_ascending(mapped_seq),
            !has_more_than_two_occurrences(mapped_seq, i as int)
    {
        let current_value = lst[i];
        let mut count = 0;
        let mut j = 0;
        
        while j < lst.len()
            invariant
                0 <= j <= lst.len(),
                count == count_occurrences(mapped_seq.take(j as int), current_value as int)
        {
            if lst[j] == current_value {
                count += 1;
                if count > 2 {
                    return false;
                }
            }
            j += 1;
        }
        
        proof {
            count_occurrences_non_negative(mapped_seq, current_value as int);
        }
        
        i += 1;
    }
    
    proof {
        sorted_from_index_implies_sorted(mapped_seq);
        no_more_than_two_equivalent(mapped_seq);
    }
    
    true
}
// </vc-code>


}

fn main() {}