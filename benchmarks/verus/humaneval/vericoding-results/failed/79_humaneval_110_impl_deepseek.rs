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

proof fn lemma_count_even_nonnegative(lst: Seq<int>)
    ensures
        count_even(lst) >= 0,
    decreases lst.len()
{
    if lst.len() == 0 {
        assert(count_even(lst) >= 0);
    } else {
        lemma_count_even_nonnegative(lst.skip(1));
        assert(count_even(lst) >= count_even(lst.skip(1)));
    }
}

proof fn lemma_count_even_cons(elem: int, rest: Seq<int>)
    ensures
        count_even(rest.cons(elem)) == (if elem % 2 == 0 {1} else {0}) + count_even(rest),
{
    assert(rest.cons(elem)@[0] == elem);
    assert(rest.cons(elem)@.skip(1) == rest@);
}

spec fn total_even_count(lst1: Seq<int>, lst2: Seq<int>) -> int {
    count_even(lst1) + count_even(lst2)
}

/* helper modified by LLM (iteration 5): Fixed view conversion for sequences */
spec fn view_to_seq_int(view: &[i8]) -> Seq<int> {
    view@.map(|x: i8| x as int)
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
    /* code modified by LLM (iteration 5): Fixed compilation error by using proper view conversion */
    ghost {
        let spec_vec1 = lst1.view().map(|_i, x| x as int);
        let spec_vec2 = lst2.view().map(|_i, x| x as int);
        lemma_count_even_nonnegative(spec_vec1);
        lemma_count_even_nonnegative(spec_vec2);
    }
    
    let total_evens_ghost = total_even_count(lst1.view().map(|_i, x| x as int), lst2.view().map(|_i, x| x as int));
    let required = lst1.len();
    
    if total_evens_ghost >= required as int {
        String::from_ascii_strict(seq!['Y', 'E', 'S'])
    } else {
        String::from_ascii_strict(seq!['N', 'O'])
    }
}
// </vc-code>


}

fn main() {}