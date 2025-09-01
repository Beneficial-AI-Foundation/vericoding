use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_fold_left_invariant(brackets: Seq<char>, i: int)
    requires 
        0 <= i <= brackets.len(),
    ensures
        ({
            let partial_result = brackets.subrange(0, i).fold_left(
                (0, true),
                |p: (int, bool), c|
                    {
                        let (x, b) = p;
                        match (c) {
                            '<' => (x + 1, b),
                            '>' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
            );
            partial_result.0 <= i && partial_result.0 >= -i
        })
{
    if i == 0 {
        assert(brackets.subrange(0, 0) === Seq::<char>::empty());
    } else {
        lemma_fold_left_invariant(brackets, i - 1);
        let prev_result = brackets.subrange(0, i - 1).fold_left(
            (0, true),
            |p: (int, bool), c|
                {
                    let (x, b) = p;
                    match (c) {
                        '<' => (x + 1, b),
                        '>' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
        );
        assert(brackets.subrange(0, i) === brackets.subrange(0, i - 1).push(brackets[i - 1]));
    }
}

proof fn lemma_fold_left_step(brackets: Seq<char>, i: int)
    requires
        0 <= i < brackets.len(),
    ensures
        ({
            let prev_result = brackets.subrange(0, i).fold_left(
                (0, true),
                |p: (int, bool), c|
                    {
                        let (x, b) = p;
                        match (c) {
                            '<' => (x + 1, b),
                            '>' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
            );
            let next_result = brackets.subrange(0, i + 1).fold_left(
                (0, true),
                |p: (int, bool), c|
                    {
                        let (x, b) = p;
                        match (c) {
                            '<' => (x + 1, b),
                            '>' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
            );
            let c = brackets[i];
            let (x, b) = prev_result;
            next_result == match (c) {
                '<' => (x + 1, b),
                '>' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        })
{
    assert(brackets.subrange(0, i + 1) === brackets.subrange(0, i).push(brackets[i]));
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)
    // pre-conditions-start
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> spec_bracketing(brackets@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut depth: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    let ghost brackets_seq = brackets@;
    
    while i < brackets_seq.len() as usize
        invariant
            0 <= i <= brackets_seq.len(),
            i <= i32::MAX,
            brackets_seq == brackets@,
            ({
                let partial_result = spec_bracketing_helper(brackets_seq.subrange(0, i as int));
                partial_result.0 == depth &&
                partial_result.1 == valid
            }),
    {
        proof {
            lemma_fold_left_step(brackets_seq, i as int);
        }
        
        let ghost c = brackets_seq[i as int];
        
        match c {
            '<' => {
                depth = depth + 1;
            }
            '>' => {
                depth = depth - 1;
                if depth < 0 {
                    valid = false;
                }
            }
            _ => {
                // no change to depth or valid
            }
        }
        
        i = i + 1;
    }
    
    assert(brackets_seq.subrange(0, brackets_seq.len() as int) === brackets_seq);
    
    valid && depth == 0
}
// </vc-code>

} // verus!
fn main() {}