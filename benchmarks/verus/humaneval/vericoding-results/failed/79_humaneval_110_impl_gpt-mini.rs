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
/* helper modified by LLM (iteration 2): lemma for appending element to sequence */
proof fn count_even_append_lemma(s: Seq<int>, x: int)
    ensures
        count_even(s + seq![x]) == count_even(s) + if x % 2 == 0 { 1 } else { 0 },
    decreases s.len()
{
    if s.len() == 0 {
        // base case: empty sequence
        // count_even(seq![x]) unfolds to if x%2==0 {1} else {0}
    } else {
        // inductive step
        count_even_append_lemma(s.skip(1), x);
    }
}

/* helper modified by LLM (iteration 2): compute_count counts even numbers in a Vec */
fn compute_count(v: &Vec<i8>) -> nat
    ensures
        result as int == count_even(v.view().map(|_i, x| x as int)),
{
    let mut i: usize = 0;
    let mut cnt: nat = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            cnt as int == count_even(v.view().slice(0, i).map(|_j, x| x as int)),
        decreases v.len() - i
    {
        let prefix = v.view().slice(0, i).map(|_j, x| x as int);
        let elem = v.index(i) as int;
        if elem % 2 == 0 {
            cnt = cnt + 1;
            proof {
                count_even_append_lemma(prefix, elem);
            }
        } else {
            proof {
                count_even_append_lemma(prefix, elem);
            }
        }
        i = i + 1;
    }
    cnt
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
    /* code modified by LLM (iteration 2): compute counts and return YES/NO accordingly */
    let c1: nat = compute_count(&lst1);
    let c2: nat = compute_count(&lst2);
    if (c1 as int + c2 as int) >= lst1.len() as int {
        String::from_str("YES")
    } else {
        String::from_str("NO")
    }
}

// </vc-code>


}

fn main() {}