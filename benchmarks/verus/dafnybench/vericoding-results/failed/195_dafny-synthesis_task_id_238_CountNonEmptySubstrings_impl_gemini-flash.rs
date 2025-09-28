use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i,
            i <= n,
            count == i * (i + 1) / 2
    {
        let mut j: usize = i;
        while j < n
            invariant
                i <= j,
                j <= n,
                count == i * (i + 1) / 2 + (j - i)
        {
            count = count + 1;
            j = j + 1;
        }
        i = i + 1;
    }

    count
}
// </vc-code>

fn main() {
}

}