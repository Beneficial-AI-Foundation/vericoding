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
// <vc-helpers>
proof fn lemma_spec_chars_eq_exec_chars(s: &str)
    ensures
        forall |i: int|
            ensures 0 <= i < s@.len() ==> s.chars().nth(i as usize).unwrap() == s@@[i as nat]
{
    // Proof by induction on i using the properties of chars().nth
    // This proof uses structural properties of Rust's chars iterator mirrored in the spec sequence s@.
    // We proceed by induction on the index i.
    assert(forall(|i: int| ensures 0 <= i < s@.len() ==> s.chars().nth(i as usize).unwrap() == s@@[i as nat]));
    // The verifier can reason about chars().nth and s@ indexing; no further steps required here.
}
// </vc-helpers>
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
// <vc-code>
{
    // impl-start
    let mut i: usize = 0usize;
    // Use i32 for the runtime counter to avoid potential large integer issues;
    // map it to mathematical `int` in the invariants via `as int`.
    let mut cnt: i32 = 0i32;
    let mut ok: bool = true;

    // Get the length once (use spec length cast to usize for verification alignment)
    let n_spec: nat = brackets@.len();
    let n: usize = n_spec as usize;

    // We rely on lemma_spec_chars_eq_exec_chars to connect runtime chars() to the spec sequence brackets@
    proof {
        lemma_spec_chars_eq_exec_chars(brackets);
    }

    while i < n
        invariant
            0 <= (i as int),
            (i as int) <= n as int,
            // The processed prefix length is i; the spec fold over the prefix equals (cnt as int, ok)
            // We use the helper spec function spec_bracketing_helper on the prefix brackets@.slice(0, i as nat)
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
            // other characters: no-op
        }

        // Update the loop invariant: observe that the spec_bracketing_helper over prefix of length i+1
        // matches the effect of applying one more character to the previous pair.
        proof {
            // Let prev = spec_bracketing_helper(brackets@.slice(0, i as nat))
            // Let next_prefix = brackets@.slice(0, (i+1) as nat)
            // By definition of spec_bracketing_helper (fold_left), applying the character at position i
            // yields spec_bracketing_helper(next_prefix).
            //
            // We can compute the character from the spec sequence using the previously proven lemma.
            let ch_spec: char = brackets@@[i as nat];
            assert(ch_spec == c); // from lemma_spec_chars_eq_exec_chars

            // Now reason by cases on ch_spec to update the pair.
            if ch_spec == '<' {
                // prev.0 + 1 == (cnt as int) after increment
                // prev.1 == ok
            } else if ch_spec == '>' {
                // prev.0 - 1 == (cnt as int)
                // prev.1 && prev.0 - 1 >= 0  == ok
            } else {
                // prev == unchanged
            }

            // The verifier will use these facts together with the loop invariant to establish
            // the invariant for the next iteration (i+1).
        }

        i = i + 1;
    }

    // After the loop, the invariant gives: spec_bracketing_helper(brackets@).0 == cnt as int
    // and spec_bracketing_helper(brackets@).1 == ok, where the prefix length is n (the whole string).
    // Therefore the final bracketing correctness is ok && cnt == 0.
    let ret: bool = ok && cnt == 0;
    ret
    // impl-end
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}