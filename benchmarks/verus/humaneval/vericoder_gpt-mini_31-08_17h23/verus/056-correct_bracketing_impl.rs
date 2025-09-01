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
proof fn lemma_spec_chars_eq_exec_chars(s: &str)
    ensures
        forall |i: int|
            0 <= i < s@.len() ==> s.chars().nth(i as usize).unwrap() == s@[i as nat]
{
    let len: nat = s@.len();
    let mut i: int = 0;
    while i < len as int
        invariant 0 <= i && i <= len as int,
        invariant (forall |j: int| 0 <= j < i ==> s.chars().nth(j as usize).unwrap() == s@[j as nat]),
        decreases (len as int) - i
    {
        let idx: usize = i as usize;
        assert(s.chars().nth(idx).unwrap() == s@[i as nat]);
        i = i + 1;
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
    let mut i: usize = 0usize;
    let mut cnt: i32 = 0i32;
    let mut ok: bool = true;

    let n_spec: nat = brackets@.len();
    let n: usize = n_spec as usize;

    proof {
        lemma_spec_chars_eq_exec_chars(brackets);
    }

    while i < n
        invariant
            0 <= (i as int),
            (i as int) <= n as int,
            spec_bracketing_helper(brackets@.slice(0, i as nat)).0 == (cnt as int),
            spec_bracketing_helper(brackets@.slice(0, i as nat)).1 == ok,
        decreases n - i
    {
        let c = brackets.chars().nth(i).unwrap();
        if c == '<' {
            cnt = cnt + 1;
        } else if c == '>' {
            cnt = cnt - 1;
            if cnt < 0 {
                ok = false;
            }
        } else {
            // no-op
        }

        proof {
            let prev = spec_bracketing_helper(brackets@.slice(0, i as nat));
            let next = spec_bracketing_helper(brackets@.slice(0, (i + 1) as nat));
            let ch_spec = brackets@[i as nat];
            assert(brackets.chars().nth(i).unwrap() == ch_spec);

            if ch_spec == '<' {
                assert(next.0 == prev.0 + 1);
                assert(next.1 == prev.1);
                assert((cnt as int) == prev.0 + 1);
                assert(ok == prev.1);
            } else if ch_spec == '>' {
                assert(next.0 == prev.0 - 1);
                assert(next.1 == (prev.1 && prev.0 - 1 >= 0));
                assert((cnt as int) == prev.0 - 1);
                // ok was updated to false iff cnt < 0, so ok == prev.1 && prev.0 - 1 >= 0
                assert(ok == (prev.1 && prev.0 - 1 >= 0));
            } else {
                assert(next == prev);
                assert((cnt as int) == prev.0);
                assert(ok == prev.1);
            }
        }

        i = i + 1;
    }

    let ret: bool = ok && cnt == 0;

    proof {
        let full = spec_bracketing_helper(brackets@);
        assert(full.0 == (cnt as int));
        assert(full.1 == ok);
        assert(spec_bracketing(brackets@) == (ok && full.0 == 0));
        assert(spec_bracketing(brackets@) == (ok && (cnt as int) == 0));
        assert(((cnt as int) == 0) == (cnt == 0));
        assert(ret == spec_bracketing(brackets@));
    }

    ret
}
// </vc-code>

} // verus!
fn main() {}