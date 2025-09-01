use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_contains_substring(s: &str, substring: &str, pos: int)
    requires
        0 <= pos <= s@.len() - substring@.len(),
        s@.subrange(pos, pos + substring@.len()) == substring@,
    ensures
        exists|j: int| 0 <= j <= s@.len() - substring@.len() && s@.subrange(j, j + substring@.len()) == substring@,
{
}

proof fn lemma_vec_push_contains<T>(v: &Vec<T>, x: T)
    ensures
        v.push(x);
        v@.contains(x),
{
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
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|k: int|
                0 <= k < i && (exists|j: int|
                    0 <= j <= strings@[k]@.len() - substring@.len() && strings[k]@.subrange(
                        j,
                        j + substring@.len(),
                    ) == substring@) ==> result@.contains(strings[k]),
    {
        let current_string = strings[i];
        let mut found = false;
        let mut j = 0;
        
        if substring.len() <= current_string.len() {
            while j <= current_string.len() - substring.len()
                invariant
                    0 <= j <= current_string@.len() - substring@.len() + 1,
                    !found ==> forall|k: int| 0 <= k < j ==> current_string@.subrange(k, k + substring@.len()) != substring@,
                    found ==> exists|k: int| 0 <= k <= current_string@.len() - substring@.len() && current_string@.subrange(k, k + substring@.len()) == substring@,
            {
                if current_string@.subrange(j as int, j as int + substring@.len()) == substring@ {
                    found = true;
                    proof {
                        lemma_contains_substring(current_string, substring, j as int);
                    }
                    break;
                }
                j += 1;
            }
        }
        
        if found {
            result.push(current_string);
            assert(result@.contains(current_string));
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}