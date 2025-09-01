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
proof fn lemma_bracketing_fold_left(
    brackets: Seq<char>,
    i: int,
    p: (int, bool),
)
    requires
        0 <= i <= brackets.len(),
        p == brackets.take(i).fold_left(
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
        ),
    ensures
        p.1 ==> forall |j: int| 0 <= j < i ==> brackets.take(j).fold_left(
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
        ).1 && brackets.take(j).fold_left(
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
        ).0 >= 0,
{
    if i == 0 {
    } else if i > 0 {
        let bracket = brackets[i - 1];
        let prev_p = brackets.take(i - 1).fold_left(
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
        assert(p == match bracket {
            '<' => (prev_p.0 + 1, prev_p.1),
            '>' => (prev_p.0 - 1, prev_p.1 && prev_p.0 - 1 >= 0),
            _ => (prev_p.0, prev_p.1),
        });
        lemma_bracketing_fold_left(brackets, i - 1, prev_p);
        if p.1 {
            assert(prev_p.1);
            if bracket == '>' {
                assert(prev_p.0 - 1 >= 0);
            }
        }
        forall |j: int| 0 <= j < i
            ensures brackets.take(j).fold_left(
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
            ).1 && brackets.take(j).fold_left(
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
            ).0 >= 0
        {
            if j < i
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
proof fn lemma_bracketing_fold_left(
    brackets: Seq<char>,
    i: int,
    p: (int, bool),
)
    requires
        0 <= i <= brackets.len(),
        p == brackets.take(i).fold_left(
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
        ),
    ensures
        p.1 ==> forall |j: int| 0 <= j < i ==> brackets.take(j).fold_left(
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
        ).1 && brackets.take(j).fold_left(
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
        ).0 >= 0,
{
    if i == 0 {
    } else if i > 0 {
        let bracket = brackets[i - 1];
        let prev_p = brackets.take(i - 1).fold_left(
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
        assert(p == match bracket {
            '<' => (prev_p.0 + 1, prev_p.1),
            '>' => (prev_p.0 - 1, prev_p.1 && prev_p.0 - 1 >= 0),
            _ => (prev_p.0, prev_p.1),
        });
        lemma_bracketing_fold_left(brackets, i - 1, prev_p);
        if p.1 {
            assert(prev_p.1);
            if bracket == '>' {
                assert(prev_p.0 - 1 >= 0);
            }
        }
        forall |j: int| 0 <= j < i
            ensures brackets.take(j).fold_left(
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
            ).1 && brackets.take(j).fold_left(
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
            ).0 >= 0
        {
            if j < i
// </vc-code>

} // verus!
fn main() {}