// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): recursive argmax index over Seq<String> by unique chars */
proof fn choose_argmax(strings: Seq<String>) -> (i: int)
    requires
        strings.len() > 0,
    ensures
        0 <= i < strings.len(),
        forall|j: int| 0 <= j < strings.len() ==> string_unique_chars(strings.index(i)@) >= string_unique_chars(strings.index(j)@),
    decreases strings.len(),
{
    if strings.len() == 1 {
        0
    } else {
        let n: int = strings.len() as int;
        assert(n >= 2);
        let pref = strings.take((n - 1) as nat);
        let i0 = choose_argmax(pref);
        let last: int = n - 1;
        if string_unique_chars(strings.index(i0)@) >= string_unique_chars(strings.index(last)@) {
            i0
        } else {
            last
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max(strings: Vec<String>) -> (s: String)
    requires 
        strings.len() > 0,
    ensures 
        exists|i: int| 0 <= i < strings.len() && #[trigger] strings@.index(i)@  s@,
        forall|i: int| 0 <= i < strings.len() ==> 
            string_unique_chars(s@) >= #[trigger] string_unique_chars(#[trigger] strings@.index(i)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): choose argmax index in ghost, then return element */
    let n = strings.len();
    proof { assert(n > 0); }
    let gi: int = choose_argmax(strings@);
    proof { assert(0 <= gi && gi < n as int); }
    let idx: usize = gi as usize;
    let s_res: String = strings[idx].clone();
    proof {
        assert(s_res@ == strings@.index(gi)@);
        assert(forall|j: int| 0 <= j < n as int ==> string_unique_chars(strings@.index(gi)@) >= string_unique_chars(strings@.index(j)@));
    }
    s_res
}
// </vc-code>


}

fn main() {}