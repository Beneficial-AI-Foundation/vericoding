// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0
}

spec fn count_survivors(n: int, a: Seq<int>) -> int {
    count_survivors_from(n, a, 0, n)
}

spec fn count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> int
    decreases n - start
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives: int = if i < left { 1 } else { 0 };
        let new_left: int = if i - a[i] < left { i - a[i] } else { left };
        survives + count_survivors_from(n, a, start + 1, new_left)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let mut left: i8 = n;
    let mut count: i8 = 0;
    let mut i: i8 = n - 1;
    
    while i >= 0
        invariant
            n >= 1,
            a.len() == n as int,
            forall|j: int| 0 <= j < n as int ==> a[j as int] >= 0,
            -1 <= i < n,
            0 <= left <= n,
            0 <= count <= n - 1 - i,
            left as int == if i >= 0 { count_survivors_from(n as int, a@.map_values(|x: i8| x as int), (n - 1 - i) as int, n as int) - count_survivors_from(n as int, a@.map_values(|x: i8| x as int), n as int, n as int) + n } else { count_survivors_from(n as int, a@.map_values(|x: i8| x as int), n as int, left as int) },
            count as int == count_survivors_from(n as int, a@.map_values(|x: i8| x as int), 0, n as int) - count_survivors_from(n as int, a@.map_values(|x: i8| x as int), (n - 1 - i) as int, left as int),
        decreases i + 1
    {
        if i < left {
            count = count + 1;
        }
        
        if i - a[i as int] < left {
            left = i - a[i as int];
        }
        
        i = i - 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}