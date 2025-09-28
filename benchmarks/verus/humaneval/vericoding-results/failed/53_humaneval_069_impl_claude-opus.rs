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

// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error - added missing semicolon */
    let mut result: i8 = -1;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < lst@.len() ==> lst@[j] > 0,
            if result == -1 {
                forall|k: int| 0 <= k < i ==> count(lst@.map(|_index: int, x: i8| x as int), lst@[k] as int) < lst@[k] as int
            } else {
                result > 0 &&
                exists|k: int| 0 <= k < i && lst@[k] == result &&
                count(lst@.map(|_index: int, x: i8| x as int), result as int) >= result as int &&
                forall|k: int| 0 <= k < i && count(lst@.map(|_index: int, x: i8| x as int), lst@[k] as int) >= lst@[k] as int ==> lst@[k] as int <= result as int
            },
        decreases lst.len() - i
    {
        let current = lst[i];
        let mut cnt: i8 = 0;
        let mut j: usize = 0;
        
        while j < lst.len()
            invariant
                0 <= j <= lst.len(),
                0 <= cnt <= 127,
                cnt as int == count(lst@.map(|_index: int, x: i8| x as int).take(j as int), current as int),
                current > 0,
            decreases lst.len() - j
        {
            if lst[j] == current {
                if cnt < 127 {
                    cnt = cnt + 1;
                }
            }
            j = j + 1;
        }
        
        assert(cnt as int == count(lst@.map(|_index: int, x: i8| x as int), current as int));
        
        if cnt >= current && current > result {
            result = current;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}