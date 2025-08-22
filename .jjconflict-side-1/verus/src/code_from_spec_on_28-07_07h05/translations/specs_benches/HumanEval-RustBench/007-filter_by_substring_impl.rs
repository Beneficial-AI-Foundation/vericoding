use vstd::prelude::*;

verus! {

fn string_eq(s1: &str, s2: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> s1@ == s2@,
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): Use Verus string view length instead of Rust str.len() */
    if s1@.len() != s2@.len() {
        return false;
    }
    
    let mut i = 0;
    while i < s1@.len()
        invariant
            0 <= i <= s1@.len(),
            s1@.len() == s2@.len(),
            forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j],
    {
        /* code modified by LLM (iteration 2): Use string view indexing instead of as_bytes() */
        if s1@[i] != s2@[i] {
            return false;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): Add assertion to help verification */
    assert(s1@ == s2@);
    true
}

fn check_substring(s: &str, sub: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= s@.len() - sub@.len() && s@.subrange(i, #[trigger] (i + sub@.len())) == sub@,
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): Use Verus string view length instead of Rust str.len() */
    if sub@.len() == 0 {
        return true;
    }
    if sub@.len() > s@.len() {
        return false;
    }
    
    let mut i = 0;
    while i <= s@.len() - sub@.len()
        invariant
            0 <= i <= s@.len() - sub@.len() + 1,
            forall|j: int| 0 <= j < i ==> s@.subrange(j, j + sub@.len()) != sub@,
    {
        /* code modified by LLM (iteration 2): Use character-by-character comparison with string view indexing */
        let mut match_found = true;
        let mut j = 0;
        while j < sub@.len()
            invariant
                0 <= j <= sub@.len(),
                match_found ==> forall|k: int| 0 <= k < j ==> s@[i + k] == sub@[k],
        {
            if s@[i + j] != sub@[j] {
                match_found = false;
                break;
            }
            j += 1;
        }
        
        if match_found {
            assert(s@.subrange(i as int, i as int + sub@.len()) == sub@);
            return true;
        }
        i += 1;
    }
    false
}

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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): Use Verus vector view length instead of Rust Vec.len() */
    while i < strings@.len()
        invariant
            0 <= i <= strings@.len(),
            forall|k: int|
                0 <= k < i && (exists|j: int|
                    0 <= j <= strings@[k]@.len() - substring@.len() && strings[k]@.subrange(
                        j,
                        j + substring@.len(),
                    ) == substring@) ==> result@.contains(strings[k]),
    {
        if check_substring(strings[i], substring) {
            result.push(strings[i]);
        }
        i += 1;
    }
    result
}

}
fn main() {}