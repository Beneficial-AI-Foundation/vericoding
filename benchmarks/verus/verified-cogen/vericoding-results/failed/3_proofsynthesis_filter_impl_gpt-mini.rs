// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive spec for filtered prefix */
spec fn filter_prefix(s: Seq<u64>, len: int) -> Seq<u64>
    requires
        0 <= len,
        len <= s.len(),
{
    if len == 0 {
        seq![]
    } else {
        let prev = filter_prefix(s, len - 1);
        if s@[len - 1] % 3 == 0 {
            prev + seq![s@[len - 1]]
        } else {
            prev
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using int index and helper filter_prefix */
    let mut i: int = 0 as int;
    while i < x.len() as int
        invariant
            0 <= i,
            i <= x.len() as int,
            y@ == filter_prefix(x@, i),
        decreases x.len() as int - i
    {
        let v: u64 = x[i as usize];
        let prev_y: Seq<u64> = y@;
        if v % 3 == 0 {
            y.push(v);
            proof {
                assert(prev_y == filter_prefix(x@, i));
                assert(prev_y + seq![v] == filter_prefix(x@, i + (1 as int)));
            }
        } else {
            proof {
                assert(prev_y == filter_prefix(x@, i));
                assert(prev_y == filter_prefix(x@, i + (1 as int)));
            }
        }
        i = i + (1 as int);
    }
}
// </vc-code>

}
fn main() {}