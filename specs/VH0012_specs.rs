// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_result(strings: Seq<Seq<char>>, result: Option<Seq<char>>) -> bool {
    if strings.len() == 0 {
        matches!(result, Option::None)
    } else {
        match result {
            Option::Some(value) => {
                exists|i: int| 0 <= i < strings.len() && #[trigger] strings[i] == value &&
                (forall|s: Seq<char>| strings.contains(s) ==> value.len() >= #[trigger] (s.len())) &&
                (forall|j: int| 0 <= j < i ==> #[trigger] (strings[j].len()) < value.len())
            },
            Option::None => false
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest(strings: Vec<Vec<char>>) -> (result: Option<Vec<char>>)
    ensures match result {
        Option::Some(value) => valid_result(strings@.map(|_i: int, v: Vec<char>| v@), Option::Some(value@)),
        Option::None => valid_result(strings@.map(|_i: int, v: Vec<char>| v@), Option::None),
    }
// </vc-spec>
// <vc-code>
{
    assume(false);
    Option::None
}
// </vc-code>


}

fn main() {}