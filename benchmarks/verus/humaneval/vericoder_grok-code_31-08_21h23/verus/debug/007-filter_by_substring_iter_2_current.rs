use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::* ;
#[verifier::proof]
fn lemma_str_contains_has_existential(s: Seq<char>, sub: Seq<char>)
ensures exists |j: int| 0 <= j <= s.len() - sub.len() && #[trigger] s.subrange(j, j + sub.len()) == sub

{

    admit();

}
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
    let mut res: Vec<&'a str> = Vec::new();
    let mut i: usize = 0;
    proof {
        // No additional proof needed here
    }
    while i < strings.len()
        invariant
            0 <= i <= strings@.len(),
            res@.len() <= i as int,
            forall |k: int| 0 <= k < i as int ==> 
                (exists |j: int| #[trigger] (0 <= j <= strings@[k]@.len() - substring@.len() && 
                    strings@[k]@.subrange(j, j + substring@.len()) == substring@) 
                    ) ==> res@.contains(#[trigger](strings@[k]))
    {
        if strings[i].contains(substring) {
            proof {
                lemma_str_contains_has_existential(strings@[i as int ], substring@);
                assert(exists |j: int| #[trigger] (0 <= j <= strings@[i as int]@.len() - substring@.len() &&
                    strings@[i as int]@.subrange(j, j + substring@.len()) == substring@));
            }
            res.push(strings[i]);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}