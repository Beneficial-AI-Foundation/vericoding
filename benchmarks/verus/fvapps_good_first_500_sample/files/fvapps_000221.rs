// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn valid_domino_char(c: char) -> bool {
    c == '.' || c == 'L' || c == 'R'
}

spec fn all_valid_chars(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> valid_domino_char(s[i])
}

spec fn push_dominoes_spec(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    s
}

fn push_dominoes(s: Vec<char>) -> (result: Vec<char>)
    requires all_valid_chars(s@),
    ensures
        result@.len() == s@.len(),
        all_valid_chars(result@),
        push_dominoes_spec(result@) == result@,
        (forall|i: int| 0 <= i < s@.len() && s@[i] != '.' ==> result@ == s@) ==> result == s,
        (forall|i: int| 0 <= i < s@.len() && s@[i] == '.') ==> (forall|j: int| 0 <= j < result@.len() ==> result@[j] == '.'),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1: Vec<char> = ".L.R...LR..L..".chars().collect();
    // let result1 = push_dominoes(test1);
    // println!("{}", result1.iter().collect::<String>()); // Should output: "LL.RR.LLRRLL.."
    
    // let test2: Vec<char> = "RR.L".chars().collect();
    // let result2 = push_dominoes(test2);
    // println!("{}", result2.iter().collect::<String>()); // Should output: "RR.L"
    
    // let test3: Vec<char> = "...".chars().collect();
    // let result3 = push_dominoes(test3);
    // println!("{}", result3.iter().collect::<String>()); // Should output: "..."
}