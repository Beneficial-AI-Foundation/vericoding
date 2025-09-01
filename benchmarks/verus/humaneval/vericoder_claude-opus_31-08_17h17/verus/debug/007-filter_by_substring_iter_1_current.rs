use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a string contains a substring
spec fn contains_substring(s: Seq<char>, sub: Seq<char>) -> bool {
    exists|j: int| 0 <= j <= s.len() - sub.len() && s.subrange(j, j + sub.len()) == sub
}

// Helper lemma to establish that if we found a match, it exists in the spec sense
proof fn substring_found_implies_exists(s: &str, sub: &str, start: usize)
    requires
        start <= s@.len() - sub@.len(),
        s@.subrange(start as int, start + sub@.len()) == sub@,
    ensures
        contains_substring(s@, sub@),
{
    assert(exists|j: int| 0 <= j <= s@.len() - sub@.len() && s@.subrange(j, j + sub@.len()) == sub@) by {
        assert(0 <= start as int <= s@.len() - sub@.len());
        assert(s@.subrange(start as int, (start as int) + sub@.len()) == sub@);
    }
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
    let mut result: Vec<&'a str> = Vec::new();
    
    for i in 0..strings.len()
        invariant
            forall|k: int| 0 <= k < i ==> 
                (contains_substring(strings@[k]@, substring@) ==> result@.contains(strings@[k])),
    {
        let s = strings[i];
        if s.len() >= substring.len() {
            let mut found = false;
            for j in 0..=(s.len() - substring.len())
                invariant
                    found ==> contains_substring(s@, substring@),
                    !found ==> forall|k: int| 0 <= k < j ==> s@.subrange(k, k + substring@.len()) != substring@,
            {
                let mut match_found = true;
                for k in 0..substring.len()
                    invariant
                        match_found <==> forall|m: int| 0 <= m < k ==> s@[j + m] == substring@[m],
                {
                    if s.get_char(j + k) != substring.get_char(k) {
                        match_found = false;
                    }
                }
                
                if match_found {
                    proof {
                        assert(s@.subrange(j as int, j + substring@.len()) == substring@) by {
                            assert forall|m: int| 0 <= m < substring@.len() implies
                                #[trigger] s@.subrange(j as int, j + substring@.len())[m] == substring@[m] by {
                                assert(s@.subrange(j as int, j + substring@.len())[m] == s@[j + m]);
                                assert(s@[j + m] == substring@[m]);
                            }
                        }
                        substring_found_implies_exists(s, substring, j);
                    }
                    found = true;
                    break;
                }
            }
            
            if found {
                result.push(s);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}