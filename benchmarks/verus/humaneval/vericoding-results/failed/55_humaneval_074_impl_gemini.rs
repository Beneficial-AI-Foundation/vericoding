// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn total_chars(lst: Seq<Seq<char>>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        lst[0].len() + total_chars(lst.subrange(1, lst.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn total_chars_int(lst: Seq<Seq<char>>) -> int
    decreases lst.len(),
{
    if lst.len() == 0 {
        0
    } else {
        lst[0].len() as int + total_chars_int(lst.subrange(1, lst.len() as int))
    }
}

#[verifier::spinoff_prover]
proof fn lemma_total_chars_as_int(s: Seq<Seq<char>>)
    ensures total_chars(s) as int == total_chars_int(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_total_chars_as_int(s.subrange(1, s.len() as int));
    }
}

#[verifier::spinoff_prover]
proof fn lemma_total_chars_int_push(s: Seq<Seq<char>>, elem: Seq<char>)
    ensures total_chars_int(s.push(elem)) == total_chars_int(s) + (elem.len() as int),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_total_chars_int_push(s.subrange(1, s.len() as int), elem);
    }
}

fn compute_total_chars_int(lst: &Vec<Vec<char>>) -> (total: int)
    ensures
        total == total_chars_int(lst@.map_values(|v: Vec<char>| v@)),
{
    let mut total: int = 0;
    let mut i: usize = 0;
    let seq_lst = lst@.map_values(|v: Vec<char>| v@);
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            total == total_chars_int(seq_lst.subrange(0, i as int)),
    {
        proof {
            let s_sub = seq_lst.subrange(0, i as int);
            let next_elem = seq_lst[i as int];
            lemma_total_chars_int_push(s_sub, next_elem);
        }
        total = total + lst[i].len() as int;
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn total_match(lst1: Vec<Vec<char>>, lst2: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures 
        result@ == lst1@ || result@ == lst2@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) <= total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst1@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) > total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst2@
// </vc-spec>
// <vc-code>
{
    let total1 = compute_total_chars_int(&lst1);
    let total2 = compute_total_chars_int(&lst2);

    proof {
        lemma_total_chars_as_int(lst1@.map_values(|v: Vec<char>| v@));
        lemma_total_chars_as_int(lst2@.map_values(|v: Vec<char>| v@));
    }

    if total1 <= total2 {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}