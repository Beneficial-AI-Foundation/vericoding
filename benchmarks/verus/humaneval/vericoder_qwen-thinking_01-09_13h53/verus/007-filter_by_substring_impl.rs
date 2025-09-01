use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn filter_by_substring<'a>(strings: &Vec<&'a str>, substring: &str) -> (res: Vec<&'a str>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < strings@.len() && (exists|j: int|
                0 <= j <= strings@[i]@.len() - substring@.len() && strings[i]@.subrange(
                    j,
                    #[trigger] (j + substring@.len()),
                ) == substring@) ==> res@.contains(#[trigger] (strings[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    let n = strings.len() as int;
    let mut i: int = 0;
    while i < n {
        invariant (0 <= i && i <= n) && (forall|j: int| 0 <= j && j < i && #[trigger] strings@[j].contains(substring) ==> res@.contains(strings@[j]));
        if strings[i as usize].contains(substring) {
            res.push(strings[i as usize]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}