// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn split_lines(s: &str) -> Seq<&str>
{
    if s.len() == 0 { seq![] } else { seq![s] }
}

spec fn split_ints(s: &str) -> Seq<int>
{
    seq![]
}

spec fn seq_to_set(s: Seq<int>) -> Set<int>
{
    s.to_set()
}

spec fn is_dangerous_group(group_data: Seq<int>) -> bool
{
    if group_data.len() <= 1 { 
        false 
    } else {
        let group_members = group_data.subrange(1, group_data.len() as int);
        let member_set = seq_to_set(group_members);
        forall|member: int| member_set.contains(member) ==> !member_set.contains(-member)
    }
}

spec fn exists_dangerous_group(stdin_input: &str) -> bool
{
    let lines = split_lines(stdin_input);
    if lines.len() == 0 { 
        false 
    } else {
        let first_line = split_ints(lines[0]);
        if first_line.len() < 2 { 
            false 
        } else {
            let n = first_line[0];
            let m = first_line[1];
            if m <= 0 || n <= 0 { 
                false 
            } else {
                exists|i: int| 1 <= i <= m && i < lines.len() && 
                    is_dangerous_group(split_ints(lines[i]))
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input.len() > 0
    ensures (result == "YES\n") || (result == "NO\n")
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO\n".to_string()
}
// </vc-code>


}

fn main() {}