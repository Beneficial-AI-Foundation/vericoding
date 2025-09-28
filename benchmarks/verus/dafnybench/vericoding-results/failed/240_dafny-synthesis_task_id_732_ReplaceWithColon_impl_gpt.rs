use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
spec fn map_replace(s: Seq<char>) -> Seq<char>
    ensures
        map_replace(s).len() == s.len(),
        forall|i: int|
            0 <= i < s.len() ==> #[trigger] map_replace(s)[i] ==
                if is_space_comma_dot(s[i]) { ':' } else { s[i] }
{
    Seq::new(s.len(), |i: int| if is_space_comma_dot(s[i]) { ':' } else { s[i] })
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    String::from_chars(map_replace(s@))
}
// </vc-code>

fn main() {}

}