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
/* helper modified by LLM (iteration 3): replaced subseq with subrange */
fn count_vec(v: &Vec<i8>, x: i8) -> (c: i32)
    requires
        v.len() < 0x7FFFFFFF,
    ensures
        c >= 0,
        c as int == count(v@.map(|_idx, val| val as int), x as int),
{
    let ghost v_int = v@.map(|_idx, val| val as int);
    let ghost x_int = x as int;
    let mut c: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            v@.map(|_idx, val| val as int) === v_int,
            x as int == x_int,
            0 <= i <= v.len(),
            c as int == count(v_int.subrange(0, i as int), x_int),
        decreases v.len() - i
    {
        if v[i] == x {
            c = c + 1;
        }
        i = i + 1;
    }
    c
}
// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): replaced subseq with subrange */
    let ghost lst_int = lst@.map(|_idx: int, x: i8| x as int);
    let mut result: i8 = -1;
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            lst_int === lst@.map(|_idx: int, x: i8| x as int),
            valid_input(lst_int),
            0 <= i <= lst.len(),
            result == -1 || lst_int.subrange(0, i as int).contains(result as int),
            result != -1 ==> (
                count(lst_int, result as int) >= result as int &&
                lst_int.contains(result as int) &&
                result > 0
            ),
            forall|y: int|
                lst_int.subrange(0, i as int).contains(y) &&
                count(lst_int, y) >= y ==> 
                y <= result as int,
        decreases lst.len() - i
    {
        let candidate = lst[i];
        if candidate > result {
            let n_occ = count_vec(&lst, candidate);
            if n_occ >= candidate as i32 {
                result = candidate;
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}