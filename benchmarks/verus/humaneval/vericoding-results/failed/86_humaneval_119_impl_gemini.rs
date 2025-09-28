// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_paren_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '(' || s[i] == ')'
}

spec fn is_balanced_helper(s: Seq<char>, depth: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        depth
    } else if s[0] == '(' {
        is_balanced_helper(s.subrange(1, s.len() as int), depth + 1)
    } else if s[0] == ')' {
        if depth > 0 {
            is_balanced_helper(s.subrange(1, s.len() as int), depth - 1)
        } else {
            -1
        }
    } else {
        is_balanced_helper(s.subrange(1, s.len() as int), depth)
    }
}

spec fn is_balanced(s: Seq<char>) -> bool {
    is_balanced_helper(s, 0) == 0
}

spec fn valid_input(lst: Seq<Seq<char>>) -> bool {
    lst.len() == 2 && valid_paren_string(lst[0]) && valid_paren_string(lst[1])
}

spec fn yes_string() -> Seq<char> {
    seq!['Y', 'e', 's']
}

spec fn no_string() -> Seq<char> {
    seq!['N', 'o']
}

spec fn correct_output(lst: Seq<Seq<char>>, result: Seq<char>) -> bool {
    (result == yes_string() || result == no_string()) &&
    (result == yes_string() <==> (is_balanced(lst[0].add(lst[1])) || is_balanced(lst[1].add(lst[0]))))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition to fix a soundness bug in the lemma */
proof fn lemma_balance_split(s1: Seq<char>, s2: Seq<char>, d: int)
    requires
        valid_paren_string(s1),
        valid_paren_string(s2),
        is_balanced_helper(s1, d) >= 0,
    ensures is_balanced_helper(s1.add(s2), d) == is_balanced_helper(s2, is_balanced_helper(s1, d)),
    decreases s1.len(),
{
    if s1.len() > 0 {
        let s1_tail = s1.subrange(1, s1.len() as int);
        if s1[0] == '(' {
            lemma_balance_split(s1_tail, s2, d + 1);
        } else { // s1[0] == ')', by valid_paren_string
            // is_balanced_helper(s1, d) >= 0 implies d > 0, so is_balanced_helper(s1_tail, d-1) >= 0
            lemma_balance_split(s1_tail, s2, d - 1);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed compilation errors by using i64 instead of int for exec code */
fn is_balanced_helper_exec(s: &Vec<char>, depth: i64) -> (result: i64)
    requires
        valid_paren_string(s@),
        depth >= 0,
    ensures result as int == is_balanced_helper(s@, depth as int),
{
    let mut current_depth = depth;
    let mut i: usize = 0;
    while i < s.len() && current_depth >= 0
        invariant
            valid_paren_string(s@),
            depth >= 0,
            i <= s.len(),
            current_depth >= 0,
            is_balanced_helper(s@, depth as int) == is_balanced_helper(s@.subrange(i as int, s.len() as int), current_depth as int),
        decreases s.len() - i
    {
        if (*s)[i] == '(' {
            current_depth = current_depth + 1;
        } else {
            current_depth = current_depth - 1;
        }
        i = i + 1;
    }
    current_depth
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using i64 instead of int for exec code */
    let s1 = &lst[0];
    let s2 = &lst[1];

    let depth1 = is_balanced_helper_exec(s1, 0);
    let mut is_balanced12 = false;
    if depth1 >= 0 {
        let final_depth12 = is_balanced_helper_exec(s2, depth1);
        if final_depth12 == 0 {
            proof {
                lemma_balance_split(s1@, s2@, 0);
            }
            is_balanced12 = true;
        }
    }

    let depth2 = is_balanced_helper_exec(s2, 0);
    let mut is_balanced21 = false;
    if depth2 >= 0 {
        let final_depth21 = is_balanced_helper_exec(s1, depth2);
        if final_depth21 == 0 {
            proof {
                lemma_balance_split(s2@, s1@, 0);
            }
            is_balanced21 = true;
        }
    }

    if is_balanced12 || is_balanced21 {
        let yes = vec!['Y', 'e', 's'];
        assert(yes@ == yes_string());
        yes
    } else {
        let no = vec!['N', 'o'];
        assert(no@ == no_string());
        no
    }
}
// </vc-code>


}

fn main() {}