// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn no_repeats(words: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < words.len() ==> words[i] != words[j]
}

spec fn consecutive_chars_match(words: Seq<Seq<char>>) -> bool 
    recommends forall|i: int| 0 <= i < words.len() ==> words[i].len() > 0
{
    forall|i: int| 0 <= i < words.len() - 1 ==> words[i][words[i].len() - 1] == words[i+1][0]
}

spec fn valid_shiritori(words: Seq<Seq<char>>) -> bool 
    recommends forall|i: int| 0 <= i < words.len() ==> words[i].len() > 0
{
    no_repeats(words) && consecutive_chars_match(words)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(words: Vec<Vec<char>>) -> (result: Vec<char>)
    requires forall|i: int| 0 <= i < words@.len() ==> words@[i].len() > 0
    ensures result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o']
    ensures (result@ == seq!['Y', 'e', 's']) <==> valid_shiritori(words@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}