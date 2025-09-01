use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

// <vc-helpers>
fn is_vowel_exec(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

#[verifier::proof]
fn lemma_is_vowel_exec_equals_spec() {
    assert forall |c: char| is_vowel(c) == is_vowel_exec(c)
        by (compute);
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let ss: Ghost<Seq<char>> = Ghost(s@);
    let mut count: u32 = 0;
    let mut i: nat = 0;
    while i < ss@.len()
        invariant
            i <= ss@.len(),
            count as int == vowels(ss@.subrange(0, i as int)).len(),
    {
        if is_vowel_exec(ss@[i as int]) {
            count = count + 1;
            assert(count as int == vowels(ss@.subrange(0, i as int + 1)).len());
        } else {
            assert(count as int == vowels(ss@.subrange(0, i as int + 1)).len());
        }
        i = i + 1;
    }
    if ss@.len() > 0 && (ss@[ss@.len() - 1] == 'y' || ss@[ss@.len() - 1] == 'Y') {
        count = count + 1;
    }
    count
}
// </vc-code>

fn main() {}
}