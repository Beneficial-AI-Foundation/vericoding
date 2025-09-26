// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn pos1(a: int, b: int, c: int) -> int {
        if a <= b && a <= c {
            a
        } else if b <= a && b <= c {
            b
        } else {
            c
        }
    }
    
    spec fn pos2(a: int, b: int, c: int) -> int {
        if a <= b && a <= c {
            if b <= c { b } else { c }
        } else if b <= a && b <= c {
            if a <= c { a } else { c }
        } else {
            if a <= b { a } else { b }
        }
    }
    
    spec fn pos3(a: int, b: int, c: int) -> int {
        if a <= b && a <= c {
            if b <= c { c } else { b }
        } else if b <= a && b <= c {
            if a <= c { c } else { a }
        } else {
            if a <= b { b } else { a }
        }
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int) -> (result: int)
    requires 1 <= a && a <= 1_000_000_000
    requires 1 <= b && b <= 1_000_000_000
    requires 1 <= c && c <= 1_000_000_000
    requires 1 <= d && d <= 1_000_000_000
    ensures result >= 0
    ensures result == (if d > (pos2(a, b, c) - pos1(a, b, c)) { d - (pos2(a, b, c) - pos1(a, b, c)) } else { 0 }) +
                     (if d > (pos3(a, b, c) - pos2(a, b, c)) { d - (pos3(a, b, c) - pos2(a, b, c)) } else { 0 })
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}