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
fn vec_max_int(v: Vec<i8>) -> (max: int)
    requires valid_input(v@.map(|x| x as int))
    ensures max == max_seq(v@.map(|x| x as int))
{
    let mut max_val = v[0] as int;
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            max_val == max_seq(v@.map(|x| x as int).subrange(0, i as int)),
    {
        if v[i] as int > max_val {
            max_val = v[i] as int;
        }
        i = i + 1;
    }
    max_val
}

fn vec_count_int(v: Vec<i8>, x: int) -> (count: int)
    ensures count == count(v@.map(|y| y as int), x)
{
    let mut c = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            c == count(v@.map(|y| y as int).subrange(0, i as int), x),
    {
        if v[i] as int == x {
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
    let max_val = vec_max_int(lst);
    let mut candidate = -1;
    let mut x = max_val;
    while x >= 1
        invariant
            1 <= x <= max_val + 1,
            candidate == -1,
            forall|y: int| x < y <= max_val ==> count(lst@.map(|z| z as int), y) < y,
        decreases x
    {
        let c = vec_count_int(lst, x);
        if c >= x {
            candidate = x;
            break;
        }
        x = x - 1;
    }
    if candidate != -1 {
        candidate as i8
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}