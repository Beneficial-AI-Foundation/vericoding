// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_even(lst: Seq<int>) -> int
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        if lst[0] % 2 == 0 {
            1 + count_even(lst.skip(1))
        } else {
            count_even(lst.skip(1))
        }
    }
}

spec fn valid_input(lst1: Seq<int>, lst2: Seq<int>) -> bool {
    lst1.len() > 0 && lst2.len() > 0
}

spec fn can_exchange(lst1: Seq<int>, lst2: Seq<int>) -> bool {
    count_even(lst1) + count_even(lst2) >= lst1.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed overflow bounds and invariant */
fn count_even_impl(lst: &Vec<i8>) -> (count: usize)
    ensures
        count == count_even(lst.view().map(|_i, x| x as int)),
        count <= lst.len(),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            count == count_even(lst.view().map(|_j, x| x as int).take(i as int)),
            count <= i,
        decreases lst.len() - i
    {
        if lst[i] % 2 == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(lst.view().map(|_j, x| x as int).take(lst.len() as int) == lst.view().map(|_j, x| x as int));
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn exchange(lst1: Vec<i8>, lst2: Vec<i8>) -> (result: String)
    requires 
        valid_input(lst1.view().map(|_i, x| x as int), lst2.view().map(|_i, x| x as int)),
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) == can_exchange(lst1.view().map(|_i, x| x as int), lst2.view().map(|_i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed overflow assertion and fixed logic */
    let count1 = count_even_impl(&lst1);
    let count2 = count_even_impl(&lst2);
    
    proof {
        assert(count1 == count_even(lst1.view().map(|_i, x| x as int)));
        assert(count2 == count_even(lst2.view().map(|_i, x| x as int)));
        assert(count1 <= lst1.len());
        assert(count2 <= lst2.len());
    }
    
    let total_even: usize = count1 + count2;
    
    proof {
        assert(total_even == count_even(lst1.view().map(|_i, x| x as int)) + count_even(lst2.view().map(|_i, x| x as int)));
    }
    
    if total_even >= lst1.len() {
        proof {
            assert(can_exchange(lst1.view().map(|_i, x| x as int), lst2.view().map(|_i, x| x as int)));
        }
        "YES".to_string()
    } else {
        proof {
            assert(!can_exchange(lst1.view().map(|_i, x| x as int), lst2.view().map(|_i, x| x as int)));
        }
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}