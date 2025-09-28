// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert Vec<i8> to Seq<int> */
spec fn to_int_seq(v: Vec<i8>) -> Seq<int> { v@.map(|i: int, x: i8| x as int) }
// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): iterative search with corrected quantifiers and invariants */
{
    let n: int = l.len() as int;
    let mut found: bool = false;
    let mut fi: int = 0;
    let mut fj: int = 0;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            if !found {
                forall|a: int, b: int|
                    (0 <= a && a < b && b < n && a < i) ==> (l[a as usize] as int) + (l[b as usize] as int) != 0,
            },
            if found {
                0 <= fi && fi < fj && fj < n,
                (l[fi as usize] as int) + (l[fj as usize] as int) == 0,
            },
        decreases n - i
    {
        let mut j: int = i + 1;
        while j < n
            invariant
                0 <= i && i < n,
                i + 1 <= j && j <= n,
                if !found {
                    forall|a: int, b: int|
                        (0 <= a && a < b && b < n && (a < i || (a == i && b < j))) ==> (l[a as usize] as int) + (l[b as usize] as int) != 0,
                },
                if found {
                    0 <= fi && fi < fj && fj < n,
                    (l[fi as usize] as int) + (l[fj as usize] as int) == 0,
                },
            decreases n - j
        {
            if !found {
                let vi: int = l[i as usize] as int;
                let vj: int = l[j as usize] as int;
                if vi + vj == 0 {
                    found = true;
                    fi = i;
                    fj = j;
                }
            }
            j = j + 1;
        }
        if found { break; }
        i = i + 1;
    }

    proof {
        if found {
            assert(0 <= fi && fi < fj && fj < n);
            assert((to_int_seq(l)@[fi] + to_int_seq(l)@[fj]) == 0);
            assert(has_pair_sum_to_zero(to_int_seq(l)));
        } else {
            assert(forall|a: int, b: int|
                (0 <= a && a < b && b < n) ==> (to_int_seq(l)@[a] + to_int_seq(l)@[b]) != 0);
            assert(!has_pair_sum_to_zero(to_int_seq(l)));
        }
    }

    found
}
// </vc-code>


}

fn main() {}