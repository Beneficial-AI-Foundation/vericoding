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
proof fn count_even_bounds(lst: Seq<int>)
    ensures
        0 <= count_even(lst) <= lst.len()
    decreases lst.len()
{
    if lst.len() == 0 {
    } else {
        count_even_bounds(lst.skip(1));
    }
}

fn count_even_exec(lst: &Vec<i8>) -> (result: usize)
    ensures
        result as int == count_even(lst.view().map(|_i, x| x as int))
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            count as int == count_even(lst.view().map(|_i, x| x as int).take(i as int))
    {
        proof {
            let full_seq = lst.view().map(|_i, x: i8| x as int);
            let prev_seq = full_seq.take(i as int);
            let next_seq = full_seq.take((i + 1) as int);
            assert(next_seq == prev_seq.push(full_seq[i as int]));
            assert(count_even(next_seq) == if full_seq[i as int] % 2 == 0 { count_even(prev_seq) + 1 } else { count_even(prev_seq) });
        }
        
        if lst[i] % 2 == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(lst.view().map(|_i, x: i8| x as int).take(lst.len() as int) == lst.view().map(|_i, x: i8| x as int));
    }
    
    count
}

/* helper modified by LLM (iteration 5): Use String::new() and push_str */
fn make_yes() -> (result: String)
    ensures
        result@ == seq!['Y', 'E', 'S']
{
    let mut s = String::new();
    s.push_str("YES");
    s
}

fn make_no() -> (result: String)
    ensures
        result@ == seq!['N', 'O']
{
    let mut s = String::new();
    s.push_str("NO");
    s
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
    /* code modified by LLM (iteration 5): Use helper functions for string creation */
    let count1 = count_even_exec(&lst1);
    let count2 = count_even_exec(&lst2);
    
    proof {
        count_even_bounds(lst1.view().map(|_i, x| x as int));
        count_even_bounds(lst2.view().map(|_i, x| x as int));
    }
    
    if count1 + count2 >= lst1.len() {
        make_yes()
    } else {
        make_no()
    }
}
// </vc-code>


}

fn main() {}