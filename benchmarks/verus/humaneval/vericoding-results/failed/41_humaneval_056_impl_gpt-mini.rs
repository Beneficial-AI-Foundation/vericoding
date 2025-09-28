// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_brackets_prefix(s: Seq<char>, end: int, bracket: char) -> int
    decreases end
{
    if end == 0 {
        0
    } else if 0 <= end <= s.len() && (bracket == '<' || bracket == '>') && s[end - 1] == bracket {
        1 + count_brackets_prefix(s, end - 1, bracket)
    } else if 0 <= end <= s.len() && (bracket == '<' || bracket == '>') {
        count_brackets_prefix(s, end - 1, bracket)
    } else {
        0
    }
}

spec fn valid_bracket_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '<' || s[i] == '>'
}

spec fn properly_nested(brackets: Seq<char>) -> bool {
    valid_bracket_string(brackets) &&
    (forall|k: int| 0 <= k <= brackets.len() ==> 
        count_brackets_prefix(brackets, k, '<') >= count_brackets_prefix(brackets, k, '>')) &&
    count_brackets_prefix(brackets, brackets.len() as int, '<') == count_brackets_prefix(brackets, brackets.len() as int, '>')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed indexing and integer literal types */
fn count_brackets_prefix_step(s: Seq<char>, k: int, bracket: char)
    requires
        0 <= k < s.len(),
        bracket == '<' || bracket == '>',
    ensures
        count_brackets_prefix(s, k + 1, bracket) == count_brackets_prefix(s, k, bracket) + (if s@[k] == bracket { 1 as int } else { 0 as int }),
{
    proof {
        if s@[k] == bracket {
            assert(count_brackets_prefix(s, k + 1, bracket) == 1 as int + count_brackets_prefix(s, k, bracket));
            assert(count_brackets_prefix(s, k + 1, bracket) == count_brackets_prefix(s, k, bracket) + (1 as int));
        } else {
            assert(count_brackets_prefix(s, k + 1, bracket) == count_brackets_prefix(s, k, bracket));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed types, indexing, and literal casts */
{
    let s = brackets@;
    let n: int = s.len() as int;
    let mut i: int = 0 as int;
    let mut balance: int = 0 as int;
    let mut ok: bool = true;

    while i < n
        invariant
            0 <= i <= n,
            0 <= balance <= n,
            ok ==> balance == count_brackets_prefix(s, i, '<') - count_brackets_prefix(s, i, '>'),
            ok ==> forall|k: int| 0 <= k <= i ==> count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>'),
        decreases n - i
    {
        let c = s@[i];
        if c == '<' {
            balance = balance + (1 as int);
            proof {
                if ok {
                    count_brackets_prefix_step(s, i, '<');
                    count_brackets_prefix_step(s, i, '>');
                    assert(count_brackets_prefix(s, i + 1, '<') == count_brackets_prefix(s, i, '<') + (if s@[i] == '<' { 1 as int } else { 0 as int }));
                    assert(count_brackets_prefix(s, i + 1, '>') == count_brackets_prefix(s, i, '>') + (if s@[i] == '>' { 1 as int } else { 0 as int }));
                }
            }
        } else {
            balance = balance - (1 as int);
            if balance < (0 as int) {
                balance = 0 as int;
                ok = false;
            } else {
                proof {
                    if ok {
                        count_brackets_prefix_step(s, i, '<');
                        count_brackets_prefix_step(s, i, '>');
                        assert(count_brackets_prefix(s, i + 1, '<') == count_brackets_prefix(s, i, '<') + (if s@[i] == '<' { 1 as int } else { 0 as int }));
                        assert(count_brackets_prefix(s, i + 1, '>') == count_brackets_prefix(s, i, '>') + (if s@[i] == '>' { 1 as int } else { 0 as int }));
                    }
                }
            }
        }
        i = i + (1 as int);
    }

    let result = ok && balance == (0 as int);

    proof {
        if result {
            assert(ok);
            assert(forall|k: int| 0 <= k <= n ==> count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>'));
            assert(count_brackets_prefix(s, n, '<') == count_brackets_prefix(s, n, '>'));
        }

        if properly_nested(s) {
            let mut j: int = 0 as int;
            let mut b: int = 0 as int;
            while j < n
                invariant
                    0 <= j <= n,
                    b == count_brackets_prefix(s, j, '<') - count_brackets_prefix(s, j, '>'),
                decreases n - j
            {
                if s@[j] == '<' {
                    b = b + (1 as int);
                } else {
                    b = b - (1 as int);
                }
                j = j + (1 as int);
            }
            assert(b == 0 as int);
        }
    }

    result
}

// </vc-code>


}

fn main() {}