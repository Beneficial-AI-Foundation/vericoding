use vstd::prelude::*;

verus! {
spec fn nesting_level(input: Seq<char>) -> (result:int)
    decreases input.len(),
{
    if input.len() == 0 {
        0
    } else {
        let prev_nesting_level = nesting_level(input.drop_last());
        let c = input.last();
        if c == '(' {
            prev_nesting_level + 1
        } else if c == ')' {
            prev_nesting_level - 1
        } else {
            prev_nesting_level
        }
    }
}
// pure-end

spec fn is_paren_char(c: char) -> (result:bool) {
    c == '(' || c == ')'
}
// pure-end

spec fn is_balanced_group(input: Seq<char>) -> (result:bool) {
    &&& input.len() > 0
    &&& nesting_level(input) == 0
    &&& forall|i| 0 <= i < input.len() ==> is_paren_char(#[trigger] input[i])
    &&& forall|i| 0 < i < input.len() ==> nesting_level(#[trigger] input.take(i)) > 0
}
// pure-end

spec fn is_sequence_of_balanced_groups(input: Seq<char>) -> (result:bool) {
    &&& nesting_level(input) == 0
    &&& forall|i| 0 < i < input.len() ==> nesting_level(#[trigger] input.take(i)) >= 0
}
// pure-end

spec fn vecs_to_seqs<T>(s: Seq<Vec<T>>) -> (result:Seq<Seq<T>>) {
    s.map(|_i, ss: Vec<T>| ss@)
}
// pure-end

spec fn remove_nonparens(s: Seq<char>) -> (result:Seq<char>) {
    s.filter(|c| is_paren_char(c))
}
// pure-end

proof fn lemma_remove_nonparens_maintained_by_push(s: Seq<char>, pos: int)
    // pre-conditions-start
    requires
        0 <= pos < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({
            let s1 = remove_nonparens(s.take(pos as int));
            let s2 = remove_nonparens(s.take((pos + 1) as int));
            if is_paren_char(s[pos]) {
                s2 == s1.push(s[pos])
            } else {
                s2 == s1
            }
        }),
    decreases pos,
    // post-conditions-end
{
    // impl-start
    reveal(Seq::filter);
    assert(s.take((pos + 1) as int).drop_last() =~= s.take(pos as int));
    if pos != 0 {
        lemma_remove_nonparens_maintained_by_push(s, pos - 1);
    }
    // impl-end
}
// pure-end

fn separate_paren_groups(input: &Vec<char>) -> (groups: Vec<Vec<char>>)
    // pre-conditions-start
    requires
        is_sequence_of_balanced_groups(input@),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int|
            #![trigger groups[i]]
            0 <= i < groups.len() ==> is_balanced_group(groups[i]@),
        vecs_to_seqs(groups@).flatten() == remove_nonparens(input@),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Added explicit type annotation to fix type inference error */
    let mut groups: Vec<Vec<char>> = Vec::new();
    let mut current_group = Vec::new();
    let mut depth = 0;
    
    /* code modified by LLM (iteration 1): Added ghost variable for loop index to fix casting error */
    let ghost mut ghost_i: int = 0;
    
    for i in 0..input.len()
        invariant
            ghost_i == i,
            forall|j: int| 0 <= j < groups.len() ==> is_balanced_group(groups[j]@),
            depth >= 0,
            depth == nesting_level(current_group@),
            vecs_to_seqs(groups@).flatten().add(current_group@) == remove_nonparens(input@.take(ghost_i)),
    {
        let c = input[i];
        if is_paren_char(c) {
            current_group.push(c);
            if c == '(' {
                depth += 1;
            } else {
                depth -= 1;
                if depth == 0 {
                    groups.push(current_group);
                    current_group = Vec::new();
                }
            }
        }
        /* code modified by LLM (iteration 1): Use ghost variable for casting in proof function call */
        lemma_remove_nonparens_maintained_by_push(input@, ghost_i);
        /* code modified by LLM (iteration 2): Fixed type mismatch by casting literal 1 to int */
        ghost_i = ghost_i + (1 as int);
    }
    
    groups
}

}
fn main() {}