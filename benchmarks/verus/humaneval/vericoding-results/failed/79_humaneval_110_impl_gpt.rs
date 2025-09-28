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
spec fn count_even_i8(lst: Seq<i8>) -> int
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        if (lst[0] as int) % 2 == 0 {
            1 + count_even_i8(lst.skip(1))
        } else {
            count_even_i8(lst.skip(1))
        }
    }
}

proof fn lemma_count_even_map_i8(lst: Seq<i8>)
    ensures
        count_even_i8(lst) == count_even(lst.map(|_i, x| x as int)),
    decreases lst.len()
{
    if lst.len() == 0 {
    } else {
        lemma_count_even_map_i8(lst.skip(1));
        if (lst[0] as int) % 2 == 0 {
            assert(lst.map(|_i, x| x as int)[0] == (lst[0] as int));
            assert(lst.map(|_i, x| x as int).skip(1) == lst.skip(1).map(|_i, x| x as int));
            assert(count_even_i8(lst) == 1 + count_even_i8(lst.skip(1)));
            assert(count_even(lst.map(|_i, x| x as int)) == 1 + count_even(lst.skip(1).map(|_i, x| x as int)));
        } else {
            assert(lst.map(|_i, x| x as int)[0] == (lst[0] as int));
            assert(lst.map(|_i, x| x as int).skip(1) == lst.skip(1).map(|_i, x| x as int));
            assert(count_even_i8(lst) == count_even_i8(lst.skip(1)));
            assert(count_even(lst.map(|_i, x| x as int)) == count_even(lst.skip(1).map(|_i, x| x as int)));
        }
    }
}

fn count_even_vec(v: &Vec<i8>) -> (res: int)
    ensures
        res == count_even_i8(v@),
{
    let mut i: usize = 0;
    let mut acc: int = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            acc == count_even_i8(v@.take(i as int)),
        decreases v.len() as int - i as int
    {
        let x = v[i];
        if (x as int) % 2 == 0 {
            acc = acc + 1;
        }
        i = i + 1;
    }
    proof {
        assert(v@.take(v.len() as int) == v@);
    }
    acc
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
    let c1 = count_even_vec(&lst1);
    let c2 = count_even_vec(&lst2);
    let len1 = lst1.len() as int;
    let feasible = c1 + c2 >= len1;

    proof {
        lemma_count_even_map_i8(lst1@);
        lemma_count_even_map_i8(lst2@);
        assert(c1 == count_even(lst1@.map(|_i, x| x as int)));
        assert(c2 == count_even(lst2@.map(|_i, x| x as int)));
        assert(feasible == can_exchange(lst1@.map(|_i, x| x as int), lst2@.map(|_i, x| x as int))); 
    }

    if feasible {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}