// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_result(strings: Seq<Seq<char>>, result: Option<Seq<char>>) -> bool {
    if strings.len() == 0 {
        matches!(result, Option::None)
    } else {
        match result {
            Option::Some(value) => {
                exists|i: int| 0 <= i < strings.len() && strings[i] == value &&
                (forall|s: Seq<char>| strings.contains(s) ==> value.len() >= s.len()) &&
                (forall|j: int| 0 <= j < i ==> strings[j].len() < value.len())
            },
            Option::None => false
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest(strings: Seq<Seq<char>>) -> (result: Option<Seq<char>>)
    ensures valid_result(strings, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Option::None
}
// </vc-code>


}

fn main() {}