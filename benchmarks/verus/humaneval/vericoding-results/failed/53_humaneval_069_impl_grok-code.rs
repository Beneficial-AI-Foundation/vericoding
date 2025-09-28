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
spec fn execcount(lst: Seq<i8>, x: i8) -> int
    requires
        x > 0
{
    lst.filter(|y| y == x).len() as int
}

/* helper modified by LLM (iteration 5): fixed lemma by removing invalid @ and adjusting map call */
proof fn execcountLem(lst: Seq<i8>, x: i8)
    requires
        x > 0
    ensures
        execcount(lst, x) == count(lst.map(|_, y: i8| y as int), x as int)
{
    assert(execcount(lst, x) == count(lst.map(|_, y: i8| y as int), x as int));
}
// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implemented frequency count using array and iterative search for the result */
    let mut freq = [0usize; 128];
    for &num in &lst {
        let idx = num as usize;
        freq[idx] += 1;
        proof { }
    }
    let mut result = -1i8;
    let mut x: i8 = 127;
    while x >= 1 
        invariant
            forall|i: usize| i >= 1 && i <= 127 ==> freq[i] == count(lst@.map(|_, v: i8| v as int), i as int),
            x >= 1 && x <= 127 || (x < 1),
            result == -1 || (result > 0 && count(lst@.map(|_, v: i8| v as int), result as int) >= (result as int))
    {
        let idx = x as usize;
        if freq[idx] >= x as usize {
            result = x;
            break;
        }
        x -= 1;
    }
    result
}
// </vc-code>


}

fn main() {}