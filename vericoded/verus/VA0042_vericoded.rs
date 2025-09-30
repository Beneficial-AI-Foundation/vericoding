// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, horizontal: Seq<char>, vertical: Seq<char>) -> bool {
    n >= 2 && n <= 20 && m >= 2 && m <= 20 &&
    horizontal.len() == n && vertical.len() == m &&
    (forall|c: char| horizontal.contains(c) ==> c == '<' || c == '>') &&
    (forall|c: char| vertical.contains(c) ==> c == '^' || c == 'v')
}

spec fn is_disconnected(hor: Seq<char>, ver: Seq<char>) -> bool {
    (hor.len() > 0 && ver.len() > 0 && hor[0] == '>' && ver[0] == 'v') ||
    (hor.len() > 0 && ver.len() > 0 && hor[0] == '<' && ver[ver.len()-1] == 'v') ||
    (hor.len() > 0 && ver.len() > 0 && hor[hor.len()-1] == '>' && ver[0] == '^') ||
    (hor.len() > 0 && ver.len() > 0 && hor[hor.len()-1] == '<' && ver[ver.len()-1] == '^')
}
// </vc-preamble>

// <vc-helpers>
fn check_disconnected(n: i8, m: i8, horizontal: &Vec<char>, vertical: &Vec<char>) -> (b: bool)
    requires
        valid_input(n as int, m as int, horizontal@, vertical@),
    ensures
        b == is_disconnected(horizontal@, vertical@),
{
    let h0 = horizontal[0];
    let hn_1 = horizontal[(n - 1) as usize];
    let v0 = vertical[0];
    let vm_1 = vertical[(m - 1) as usize];

    (h0 == '>' && v0 == 'v') ||
    (h0 == '<' && vm_1 == 'v') ||
    (hn_1 == '>' && v0 == '^') ||
    (hn_1 == '<' && vm_1 == '^')
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, horizontal: Vec<char>, vertical: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(n as int, m as int, horizontal@, vertical@)
    ensures 
        result@ == seq!['Y', 'E', 'S', '\n'] || result@ == seq!['N', 'O', '\n'],
        (result@ == seq!['N', 'O', '\n']) <==> is_disconnected(horizontal@, vertical@)
// </vc-spec>
// <vc-code>
{
    if check_disconnected(n, m, &horizontal, &vertical) {
        vec!['N', 'O', '\n']
    } else {
        vec!['Y', 'E', 'S', '\n']
    }
}
// </vc-code>


}

fn main() {}