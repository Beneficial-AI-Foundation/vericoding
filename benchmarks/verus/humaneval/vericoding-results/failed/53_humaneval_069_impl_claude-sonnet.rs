// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

spec fn count(s: Seq<int>, x: int) -> int {
    s.filter(|i: int| i == x).len() as int
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 { s[0] } else { choose|x: int| s.contains(x) }
}

spec fn valid_input(lst: Seq<int>) -> bool {
    lst.len() > 0 && forall|i: int| 0 <= i < lst.len() ==> lst[i] > 0
}

spec fn valid_result(lst: Seq<int>, result: int) -> bool
    recommends valid_input(lst)
{
    if result == -1 {
        forall|x: int| #![auto] lst.contains(x) ==> count(lst, x) < x
    } else {
        result > 0 &&
        lst.contains(result) && 
        count(lst, result) >= result &&
        forall|y: int| #![auto] lst.contains(y) && count(lst, y) >= y ==> y <= result
    }
}

// <vc-helpers>
fn count_occurrences(lst: &Vec<i8>, x: i8) -> (result: usize)
    requires lst@.len() > 0
    ensures result as int == count(lst@.map(|_index: int, val: i8| val as int), x as int)
{
    let mut count_var = 0;
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            count_var as int == count(lst@.subrange(0, i as int).map(|_index: int, val: i8| val as int), x as int)
    {
        if lst[i] == x {
            count_var += 1;
        }
        i += 1;
    }
    count_var
}

/* helper modified by LLM (iteration 5): fixed lemma syntax by adding proof block */
proof fn count_properties(s: Seq<int>, x: int)
    ensures count(s, x) >= 0,
            count(s, x) <= s.len()
{
}

proof fn valid_result_unique(lst: Seq<int>, result1: int, result2: int)
    requires valid_input(lst),
             valid_result(lst, result1),
             valid_result(lst, result2),
             result1 != -1,
             result2 != -1
    ensures result1 == result2
{
}
// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed variable naming conflicts and type issues */
    let mut max_valid = -1i8;
    let mut found_any = false;
    
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            max_valid == -1 || (max_valid > 0 && lst@.contains(max_valid)),
            max_valid == -1 || count(lst@.map(|_index: int, x: i8| x as int), max_valid as int) >= max_valid as int,
            max_valid == -1 || forall|y: int| #![auto] 0 <= y < i ==> lst@[y] <= max_valid as int || count(lst@.map(|_index: int, x: i8| x as int), y) < y,
            found_any <==> max_valid != -1
    {
        let current = lst[i];
        let occurrences = count_occurrences(&lst, current);
        
        if occurrences >= current as usize {
            if !found_any || current > max_valid {
                max_valid = current;
                found_any = true;
            }
        }
        
        i += 1;
    }
    
    max_valid
}
// </vc-code>


}

fn main() {}