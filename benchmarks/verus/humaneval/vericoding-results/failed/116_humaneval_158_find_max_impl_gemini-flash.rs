// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_max(strings: Vec<String>) -> (s: String)
    requires 
        strings.len() > 0,
    ensures 
        exists|i: int| 0 <= i < strings.len() && #[trigger] strings@.index(i)@ == s@,
        forall|i: int| 0 <= i < strings.len() ==> 
            string_unique_chars(s@) >= #[trigger] string_unique_chars(#[trigger] strings@.index(i)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected `String::view()` to `String::reveal_str().view()` so it returns a `Seq<char>` directly without errors. */
    assert(strings.len() > 0);

    let mut max_s: String = strings[0].clone();
    let mut max_unique_chars: int = string_unique_chars(strings[0].reveal_str().view());

    let mut i: usize = 1;
    while i < strings.len()
        invariant
            0 <= (i as int),
            (i as int) <= (strings.len() as int),
            exists|k: int| 0 <= k < (i as int) && #[trigger] strings@.index(k)@ == max_s@,
            forall|j: int| 0 <= j < (i as int) ==> string_unique_chars(max_s@) >= #[trigger] string_unique_chars(#[trigger] strings@.index(j)@),
            max_unique_chars == string_unique_chars(max_s@),
        decreases strings.len() - i
    {
        let current_s = strings[i].clone();
        let current_unique_chars: int = string_unique_chars(current_s.reveal_str().view());

        if current_unique_chars > max_unique_chars {
            max_unique_chars = current_unique_chars;
            max_s = current_s;
        }
        i = i + 1;
    }
    max_s
}
// </vc-code>


}

fn main() {}