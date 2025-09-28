// <vc-preamble>
use vstd::prelude::*;

verus! {

/* SFC64 state containing 256 bits split into four 64-bit words */
struct SFC64State {
    a: u64,
    b: u64,
    c: u64,
    counter: u64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Replaced unsupported rotate_left with equivalent bitwise operations. */
fn step(st: SFC64State) -> (new_st: SFC64State)
    ensures
        new_st.counter == st.counter.wrapping_add(1),
{
    let result = st.a.wrapping_add(st.b).wrapping_add(st.counter);
    let new_a = st.b ^ (st.b >> 11);
    let new_b = st.c.wrapping_add(st.c << 3);
    let new_c = ((st.c << 24) | (st.c >> 40)).wrapping_add(result);
    let new_counter = st.counter.wrapping_add(1);

    SFC64State { a: new_a, b: new_b, c: new_c, counter: new_counter }
}
// </vc-helpers>

// <vc-spec>
fn sfc64(seed: Option<u64>) -> (state: SFC64State)
    ensures
        seed.is_none() ==> (state.a == 0 && state.b == 0 && state.c == 0 && state.counter == 0),
        seed.is_some() ==> (state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): No logical changes; relying on helper fix for compilation. */
    match seed {
        None => {
            SFC64State { a: 0, b: 0, c: 0, counter: 0 }
        },
        Some(s) => {
            let mut st = SFC64State { a: s, b: s, c: s, counter: 1 };

            let mut i: u64 = 0;
            while i < 12
                invariant
                    i <= 12,
                    st.counter == 1u64.wrapping_add(i),
                decreases 12 - i
            {
                st = step(st);
                i = i + 1;
            }
            st
        }
    }
}
// </vc-code>


}
fn main() {}