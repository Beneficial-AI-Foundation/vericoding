// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn odd_or_zero_int(x: u32) -> int {
    if x % 2 == 0 {
        x as int
    } else {
        0
    }
}

proof fn add_odd_evens_nonneg(s: Seq<u32>) ensures add_odd_evens(s) >= 0 {
}

// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
{
    let s = lst@;
    let mut i: nat = 0;
    let mut acc: int = 0;
    while i < lst.len()
        invariant
            0 <= acc,
            acc + add_odd_evens(s.skip(i)) == add_odd_evens(s),
        decreases lst.len() - i
    {
        if i + 1 < lst.len() {
            let v: u32 = lst.get(i + 1);
            let add_val: u32 = if v % 2 == 0 { v } else { 0 };
            acc = acc + (add_val as int);
        }
        i = i + 2;
    }
    let sum = acc as u64;
    sum
}

// </vc-code>

}
fn main() {}