// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ghost function syntax */
fn pad_string(s: Seq<char>, width: nat, fillchar: char) -> (result: Seq<char>)
    ensures
        result.len() == if s.len() >= width { s.len() } else { width },
        s.len() >= width ==> result == s,
        s.len() < width ==> {
            &&& result.len() == width
            &&& result.subrange(0, s.len() as int) == s
            &&& forall|j: int| s.len() <= j < width ==> result[j] == fillchar
        }
{
    if s.len() >= width {
        s
    } else {
        let mut result = Seq::empty();
        let mut i: int = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == s[j]
        {
            result = result.push(s[i]);
            i = i + 1;
        }
        let mut j: int = 0;
        while j < width - s.len()
            invariant
                0 <= j <= width - s.len(),
                result.len() == s.len() + j,
                forall|k: int| 0 <= k < s.len() ==> result[k] == s[k],
                forall|k: int| s.len() <= k < s.len() + j ==> result[k] == fillchar
        {
            result = result.push(fillchar);
            j = j + 1;
        }
        result
    }
}
ghost fn ghost_width(width: u8) -> nat {
    width as nat
}
// </vc-helpers>

// <vc-spec>
fn ljust(a: Vec<String>, width: u8, fillchar: char) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == if a[i]@.len() >= width as nat { a[i]@.len() } else { width as nat },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() >= width as nat ==> #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() && a[i]@.len() < width as nat ==> {
            &&& #[trigger] result[i]@.len() == width as nat
            &&& result[i]@.subrange(0, a[i]@.len() as int) == a[i]@
        },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == width as nat
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed ghost function call syntax */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j]@.len() == if a[j]@.len() >= ghost_width(width) { a[j]@.len() } else { ghost_width(width) },
            forall|j: int| 0 <= j < result.len() && a[j]@.len() >= ghost_width(width) ==> #[trigger] result[j]@ == a[j]@,
            forall|j: int| 0 <= j < result.len() && a[j]@.len() < ghost_width(width) ==> {
                &&& #[trigger] result[j]@.len() == ghost_width(width)
                &&& result[j]@.subrange(0, a[j]@.len() as int) == a[j]@
            }
    {
        let s = &a[i];
        let padded = pad_string(s@, ghost_width(width), fillchar);
        let mut chars = Vec::new();
        let mut idx: int = 0;
        while idx < padded.len()
            invariant
                0 <= idx <= padded.len(),
                chars.len() == idx,
                forall|k: int| 0 <= k < idx ==> chars[k] == padded[k]
        {
            chars.push(padded[idx]);
            idx = idx + 1;
        }
        let new_string = String::from_chars(chars);
        result.push(new_string);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}