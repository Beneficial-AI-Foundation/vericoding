// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_letter(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && (('A' <= s[i] && s[i] <= 'Z') || ('a' <= s[i] && s[i] <= 'z'))
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s 
    } else { 
        s.subrange(s.len() as int - 1, s.len() as int).add(reverse_string(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn swap_case(c: char) -> char
{
    if 'A' <= c && c <= 'Z' { 
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' { 
        ((c as u32 - 32) as char)
    } else { 
        c 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add predicate to recognize letters (unchanged behavior) */
spec fn is_letter_char(c: char) -> bool
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

/* helper modified by LLM (iteration 5): lemma stating pointwise equality of reverse_string */
proof fn lemma_reverse_pointwise(s: Seq<char>)
    ensures
        reverse_string(s).len() == s.len(),
        forall|i: int| 0 <= i && i < s.len() ==> reverse_string(s)[i] == s[s.len() - 1 - i],
    decreases s.len()
{
    if s.len() == 0 {
        assert(reverse_string(s) == s);
    } else {
        let n = s.len();
        let last = s.subrange(n - 1, n);
        let prefix = s.subrange(0, n - 1);
        lemma_reverse_pointwise(prefix);
        assert(reverse_string(s) == last.add(reverse_string(prefix)));
        assert(last.len() == 1);
        assert(reverse_string(prefix).len() == prefix.len());
        assert(prefix.len() == n - 1);
        assert forall|i: int| 0 <= i && i < n ==> reverse_string(s)[i] == s[n - 1 - i] by {
            assert(reverse_string(s) == last.add(reverse_string(prefix)));
            if i == 0 {
                assert(i < last.len());
                assert(reverse_string(s)[i] == last.add(reverse_string(prefix))[i]);
                assert(last.add(reverse_string(prefix))[i] == last[i]);
                assert(last[i] == s[n - 1]);
                assert(s[n - 1 - i] == s[n - 1]);
            } else {
                assert(0 < i);
                assert(i >= last.len());
                assert(i < n);
                assert(reverse_string(s)[i] == last.add(reverse_string(prefix))[i]);
                assert(last.add(reverse_string(prefix))[i] == reverse_string(prefix)[i - last.len()]);
                assert(i - last.len() < reverse_string(prefix).len());
                assert(reverse_string(prefix)[i - last.len()] == prefix[prefix.len() - 1 - (i - last.len())]);
                assert(prefix.len() == n - 1);
                assert(0 <= n - 1 - i && n - 1 - i < prefix.len());
                assert(prefix[prefix.len() - 1 - (i - last.len())] == prefix[n - 1 - i]);
                assert(prefix[n - 1 - i] == s[n - 1 - i]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures (if has_letter(s@) {
        result@.len() == s@.len() && 
        (forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]))
    } else {
        result@ == reverse_string(s@)
    }) && result@.len() == s@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix quantifier syntax and decreases types; implement case-swap or reverse */
    let n: usize = s.len();
    let n_int: int = n as int;

    let mut found: bool = false;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            found == exists|j: int| 0 <= j < i as int && ((('A' <= s@[j] && s@[j] <= 'Z') || ('a' <= s@[j] && s@[j] <= 'z'))),
        decreases (n - i) as int
    {
        assert(i < n);
        let c = s[i];
        if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
            found = true;
        }
        i += 1;
    }
    proof {
        assert(i == n);
        assert(found == exists|j: int| 0 <= j < s@.len() && ((('A' <= s@[j] && s@[j] <= 'Z') || ('a' <= s@[j] && s@[j] <= 'z'))));
        assert(found == has_letter(s@));
    }

    if found {
        let mut r: Vec<char> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                r@.len() == k as int,
                forall|j: int| 0 <= j && j < k as int ==> r@[j] == swap_case(s@[j]),
            decreases (n - k) as int
        {
            assert(k < n);
            let c = s[k];
            let sc = if ('A' <= c && c <= 'Z') { (((c as u32) + 32) as char) } else if ('a' <= c && c <= 'z') { (((c as u32) - 32) as char) } else { c };
            proof { assert(sc == swap_case(c)); }
            r.push(sc);
            k += 1;
        }
        proof { assert(k == n); }
        r
    } else {
        proof { lemma_reverse_pointwise(s@); }
        let mut r: Vec<char> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                r@.len() == k as int,
                forall|j: int| 0 <= j && j < k as int ==> r@[j] == s@[n as int - 1 - j],
            decreases (n - k) as int
        {
            let idx = n - 1 - k;
            assert(idx < n);
            let c = s[idx];
            r.push(c);
            k += 1;
        }
        proof {
            assert(r@.len() == s@.len());
            assert(reverse_string(s@).len() == s@.len());
            assert forall|i0: int| 0 <= i0 && i0 < r@.len() ==> r@[i0] == reverse_string(s@)[i0] by {
                assert(r@[i0] == s@[n as int - 1 - i0]);
                assert(reverse_string(s@)[i0] == s@[s@.len() - 1 - i0]);
                assert(s@.len() == n_int);
                assert(reverse_string(s@)[i0] == s@[n as int - 1 - i0]);
            }
            assert(r@ == reverse_string(s@));
        }
        r
    }
}
// </vc-code>


}

fn main() {}