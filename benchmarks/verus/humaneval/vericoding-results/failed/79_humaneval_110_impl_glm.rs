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
/* helper modified by LLM (iteration 4): fixed subrange call to use int instead of nat for end index */
fn count_even_vec(v: Vec<i8>) -> (count: usize)
    ensures (count as nat) == count_even(v.view().map(|_i, x| x as int))
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            (count as nat) == count_even(v.view().subrange(0, i as int).map(|_i, x| x as int)),
        decreases v.len() - i
    {
        let x = v[i];
        if x % 2 == 0 {
            count += 1;
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): replaced String::from with to_string to avoid compilation error */
    let even1 = count_even_vec(lst1);
    let even2 = count_even_vec(lst2);
    if even1 + even2 >= lst1.len() {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}