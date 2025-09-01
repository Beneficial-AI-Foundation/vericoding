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
proof fn lemma_fold_left_associative<A, B, C>(
    seq: Seq<A>,
    init: B,
    f: spec_fn(A, B) -> C,
    g: spec_fn(B, C) -> B,
)
    requires
        forall|i: int, x: A, y: B| g(f(x, y), init) == g(y, f(x, init)),
    ensures
        seq.fold_left(init, |acc, a| g(f(a, acc), init)) == g(seq.fold_left(init, f), init),
{
    reveal(seq.fold_left);
    if seq.len() == 0 {
    } else {
        let seq_pop = seq.pop_last();
        let last = seq.last();
        lemma_fold_left_associative(seq_pop, init, f, g);
        calc! {
            (==)
            seq.fold_left(init, |acc, a| g(f(a, acc), init));
            seq_pop.fold_left(init, |acc, a| g(f(a, acc), init)).fold_left(init, |acc, a| g(f(a, acc), init));
            { lemma_fold_left_associative(seq_pop, init, f, g); }
            g(seq_pop.fold_left(init, f), init).fold_left(init, |acc, a| g(f(a, acc), init));
            g(seq_pop.fold_left(init, f), init.fold_left(init, f));
            g(seq_pop.fold_left(init, f), init);
            { reveal(seq.fold_left); }
            seq.fold_left(init, f);
        }
    }
}

proof fn lemma_bracketing_helper_fold(
    s: Seq<char>,
    state: (int, bool),
)
    ensures
        (s.push('(')).fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) == match s.fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) {
            (x, b) => (x + 1, b),
        },
{
    reveal(spec_bracketing_helper);
    if s.len() == 0 {
    } else {
        let s_pop = s.pop_last();
        let last = s.last();
        lemma_bracketing_helper_fold(s_pop, state);
        calc! {
            (==)
            (s.push('(')).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push(last).push('(').fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push('(').push(last).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            {
                let fresh_state = s_pop.fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                lemma_bracketing_helper_fold(s_pop, state);
                let (x, b) = fresh_state;
                assert(s_pop.push('(').fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == (x+1, b));
                let new_state = s_pop.push('(').fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                assert(s_pop.push('(').push(last).fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                });
                match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                }
            };
            match s.fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            ) {
                (x, b) => (x + 1, b),
            }
        }
    }
}

proof fn lemma_bracketing_helper_fold_paren(
    s: Seq<char>,
    state: (int, bool),
)
    ensures
        (s.push(')')).fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) == match s.fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) {
            (x, b) => (x - 1, b && x - 1 >= 0),
        },
{
    reveal(spec_bracketing_helper);
    if s.len() == 0 {
    } else {
        let s_pop = s.pop_last();
        let last = s.last();
        lemma_bracketing_helper_fold_paren(s_pop, state);
        calc! {
            (==)
            (s.push(')')).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push(last).push(')').fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push(')').push(last).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            {
                let fresh_state = s_pop.fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                lemma_bracketing_helper_fold_paren(s_pop, state);
                let (x, b) = fresh_state;
                assert(s_pop.push(')').fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == (x-1, b && x-1 >= 0));
                let new_state = s_pop.push(')').fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                assert(s_pop.push(')').push(last).fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                });
                match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                }
            };
            match s.fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            ) {
                (x, b) => (x - 1, b && x - 1 >= 0),
            }
        }
    }
}

proof fn lemma_bracketing_helper_fold_other(
    s: Seq<char>,
    state: (int, bool),
    c: char,
)
    requires
        c != '(' && c != ')',
    ensures
        (s.push(c)).fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) == match s.fold_left(
            state,
            |p: (int, bool), c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        ) {
            (x, b) => (x, b),
        },
{
    reveal(spec_bracketing_helper);
    if s.len() == 0 {
    } else {
        let s_pop = s.pop_last();
        let last = s.last();
        lemma_bracketing_helper_fold_other(s_pop, state, c);
        calc! {
            (==)
            (s.push(c)).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push(last).push(c).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            s_pop.push(c).push(last).fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            );
            {
                let fresh_state = s_pop.fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                lemma_bracketing_helper_fold_other(s_pop, state, c);
                let (x, b) = fresh_state;
                assert(s_pop.push(c).fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == (x, b));
                let new_state = s_pop.push(c).fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                );
                assert(s_pop.push(c).push(last).fold_left(
                    state,
                    |p: (int, bool), c| {
                        let (x, b) = p;
                        match c {
                            '(' => (x + 1, b),
                            ')' => (x - 1, b && x - 1 >= 0),
                            _ => (x, b),
                        }
                    },
                ) == match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                });
                match new_state {
                    (x_n, b_n) => match last {
                        '(' => (x_n + 1, b_n),
                        ')' => (x_n - 1, b_n && x_n - 1 >= 0),
                        _ => (x_n, b_n),
                    },
                }
            };
            match s.fold_left(
                state,
                |p: (int, bool), c| {
                    let (x, b) = p;
                    match c {
                        '(' => (x + 1, b),
                        ')' => (x - 1, b && x - 1 >= 0),
                        _ => (x, b),
                    }
                },
            ) {
                (x, b) => (x, b),
            }
        }
    }
}

proof fn lemma_spec_bracketing_helper_indexed(
    brackets: Seq<char>,
    i: int,
)
    requires
        0 <= i <= brackets.len(),
    ensures
        spec_bracketing_helper(brackets.take(i)) == brackets.take(i).fold_left(
            (0, true),
            |p, c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        )
        && spec_bracketing_helper(brackets.take(i)).0 >= 0,
{
    reveal(spec_bracketing_helper);
    if i == 0 {
    } else {
        lemma_spec_bracketing_helper_indexed(brackets, i - 1);
        let prev_seq = brackets.take(i - 1);
        let prev_res = spec_bracketing_helper(prev_seq);
        assert(prev_seq.len() == i - 1);
        assert(brackets.take(i) == prev_seq.push(brackets@[i - 1]));
        let c = brackets@[i - 1];
        let prev_fold = prev_seq.fold_left(
            (0, true),
            |p, c| {
                let (x, b) = p;
                match c {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
        );
        assert(prev_res == prev_fold);
        assert(prev_res.0 >= 0);

        let new_res = spec_bracketing_helper(brackets.take(i));
        if c == '(' {
            lemma_bracketing_helper_fold(prev_seq, (0, true));
            assert(new_res == (prev_res.0 + 1, prev_res.1));
        } else if c == ')' {
            lemma_bracketing_helper_fold_paren(prev_seq, (0, true));
            assert(new_res == (prev_res.0 - 1, prev_res.1 && prev_res.0 - 1 >= 0));
        } else {
            lemma_bracketing_helper_fold_other(prev_seq, (0, true), c);
            assert(new_res == prev_res);
        }
        assert(new_res.0 >= 0);
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
    let mut current_count: int = 0;
    let mut valid_so_far: bool = true;
    let chars_seq = brackets@;

    for i in 0..brackets.len()
        invariant
            0 <= i <= brackets.len(),
            spec_bracketing_helper(chars_seq.take(i)) == (current_count, valid_so_far),
            current_count >= 0,
    {
        let c = brackets.chars().nth(i).unwrap();
        proof {
            lemma_spec_bracketing_helper_indexed(chars_seq, i);
            assert(chars_seq.take(i+1) == chars_seq.take(i).push(c));
        }

        if c == '(' {
            current_count = current_count + 1;
        } else if c == ')' {
            let old_count = current_count;
            proof {
                assert(old_count >= 0);
            }
            current_count = current_count - 1;
            valid_so_far = valid_so_far && old_count >= 1;
        }
        proof {
            reveal(spec_bracketing_helper);
            if c == '(' {
                lemma_bracketing_helper_fold(chars_seq.take(i), (0, true));
            } else if c == ')' {
                lemma_bracketing_helper_fold_paren(chars_seq.take(i), (0, true));
            } else {
                lemma_bracketing_helper_fold_other(chars_seq.take(i), (0, true), c);
            }
        }
    }

    proof {
        lemma_spec_bracketing_helper_indexed(chars_seq, brackets.len());
    }
    current_count == 0 && valid_so_far
}
// </vc-code>

} // verus!
fn main() {}