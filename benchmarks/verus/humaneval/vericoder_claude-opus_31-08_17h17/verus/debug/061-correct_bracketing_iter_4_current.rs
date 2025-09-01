use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (ret:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_bracketing_helper_equiv(brackets: Seq<char>, i: nat)
    requires
        i <= brackets.len(),
    ensures
        spec_bracketing_helper(brackets.subrange(0, i as int)) == 
        brackets.subrange(0, i as int).fold_left(
            (0, true),
            |p: (int, bool), c| {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            }
        ),
    decreases i,
{
    if i == 0 {
        assert(brackets.subrange(0, 0) =~= Seq::<char>::empty());
    } else {
        lemma_bracketing_helper_equiv(brackets, (i - 1) as nat);
        assert(brackets.subrange(0, i as int) =~= 
               brackets.subrange(0, (i - 1) as int).push(brackets[(i - 1) as int]));
    }
}

proof fn lemma_bracketing_append(brackets: Seq<char>, c: char)
    ensures
        spec_bracketing_helper(brackets.push(c)) == {
            let (x, b) = spec_bracketing_helper(brackets);
            match c {
                '(' => (x + 1, b),
                ')' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        }
{
    reveal(Seq::fold_left);
    assert(brackets.push(c).fold_left(
        (0, true),
        |p: (int, bool), ch| {
            let (x, b) = p;
            match ch {
                '(' => (x + 1, b),
                ')' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        }
    ) == {
        let init_result = brackets.fold_left(
            (0, true),
            |p: (int, bool), ch| {
                let (x, b) = p;
                match ch {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            }
        );
        let (x, b) = init_result;
        match c {
            '(' => (x + 1, b),
            ')' => (x - 1, b && x - 1 >= 0),
            _ => (x, b),
        }
    });
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
            ({
                let (spec_depth, spec_valid) = spec_bracketing_helper(brackets@.subrange(0, i as int));
                depth == spec_depth && valid == spec_valid
            }),
            depth >= -i,
            depth <= i,
        decreases brackets@.len() - i,
    {
        let c = brackets.get_char(i);
        
        proof {
            lemma_bracketing_append(brackets@.subrange(0, i as int), c);
            assert(brackets@.subrange(0, (i + 1) as int) =~= 
                   brackets@.subrange(0, i as int).push(c));
        }
        
        if c == '(' {
            depth = depth + 1;
        } else if c == ')' {
            depth = depth - 1;
            if depth < 0 {
                valid = false;
            }
        }
        
        i = i + 1;
    }
    
    assert(brackets@.subrange(0, brackets@.len() as int) =~= brackets@);
    valid && depth == 0
}
// </vc-code>

} // verus!
fn main() {}