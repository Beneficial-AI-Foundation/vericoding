use vstd::prelude::*;

verus! {

fn string_eq(s1: &str, s2: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> s1@ == s2@,
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

fn check_substring(s: &str, sub: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= s@.len() - sub@.len() && s@.subrange(i, #[trigger] (i + sub@.len())) == sub@,
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}
fn main() {}
