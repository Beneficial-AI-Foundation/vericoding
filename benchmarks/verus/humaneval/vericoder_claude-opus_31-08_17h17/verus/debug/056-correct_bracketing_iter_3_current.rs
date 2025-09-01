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
proof fn lemma_bracketing_helper_equiv(brackets: Seq<char>, i: int)
    requires
        0 <= i <= brackets.len(),
    ensures
        spec_bracketing_helper(brackets.subrange(0, i)) == 
        brackets.subrange(0, i).fold_left(
            (0, true),
            |p: (int, bool), c| {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            }
        ),
    decreases i,
{
    if i == 0 {
        assert(brackets.subrange(0, 0) =~= Seq::<char>::empty());
    } else {
        lemma_bracketing_helper_equiv(brackets, i - 1);
        assert(brackets.subrange(0, i) =~= brackets.subrange(0, i - 1).push(brackets[i - 1]));
    }
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
    let mut valid = true;
    let mut i: usize = 0;
    
    while i < brackets.unicode_len()
        invariant
            i <= brackets@.len(),
            brackets@.len() <= i32::MAX,
            -brackets@.len() >= i32::MIN,
            depth >= i32::MIN,
            depth <= i32::MAX,
            ({
                let result = spec_bracketing_helper(brackets@.subrange(0, i as int));
                depth == result.0 && valid == result.1
            }),
    {
        let c = brackets.get_char(i);
        
        if c == '<' {
            depth = depth + 1;
        } else if c == '>' {
            depth = depth - 1;
            if depth < 0 {
                valid = false;
            }
        }
        
        i = i + 1;
        
        proof {
            lemma_bracketing_helper_equiv(brackets@, i as int);
            let prev_result = spec_bracketing_helper(brackets@.subrange(0, (i - 1) as int));
            let curr_result = spec_bracketing_helper(brackets@.subrange(0, i as int));
            assert(brackets@.subrange(0, i as int) =~= 
                   brackets@.subrange(0, (i - 1) as int).push(brackets@[(i - 1) as int]));
        }
    }
    
    proof {
        assert(brackets@.subrange(0, brackets@.len() as int) =~= brackets@);
    }
    
    valid && depth == 0
}
// </vc-code>

} // verus!
fn main() {}