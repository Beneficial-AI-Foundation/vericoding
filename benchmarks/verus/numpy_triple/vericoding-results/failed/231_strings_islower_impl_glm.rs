// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn exec_is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

fn exec_is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

proof fn lemma_exec_is_alpha_char(c: char)
    ensures
        exec_is_alpha_char(c) == is_alpha_char(c)
{
    assert(exec_is_alpha_char(c) == (('a' <= c <= 'z') || ('A' <= c <= 'Z')));
}

proof fn lemma_exec_is_lower_char(c: char)
    ensures
        exec_is_lower_char(c) == is_lower_char(c)
{
    assert(exec_is_lower_char(c) == ('a' <= c <= 'z'));
}

/* helper modified by LLM (iteration 5): fixed sequence indexing by using vector of characters */
fn check_string(s: String) -> (b: bool)
    ensures
        b == (string_has_cased_char(s@) && string_all_cased_are_lowercase(s@))
{
    let mut has_cased = false;
    let mut all_lower = true;
    let n = s.len() as int;
    let chars_vec: Vec<char> = s.chars().collect();
    let mut i = 0;

    while i < n
        invariant
            0 <= i <= n,
            has_cased == (exists|j: int| 0 <= j < i && exec_is_alpha_char(chars_vec[j as usize])),
            all_lower == (forall|j: int| 0 <= j < i && exec_is_alpha_char(chars_vec[j as usize]) ==> exec_is_lower_char(chars_vec[j as usize])),
        decreases n - i
    {
        let c = chars_vec[i as usize];
        if exec_is_alpha_char(c) {
            has_cased = true;
            if !exec_is_lower_char(c) {
                all_lower = false;
            }
        }
        i += 1;
    }

    proof {
        assert(s@ == chars_vec@);

        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|k: int| 0 <= k < j ==> exec_is_alpha_char(chars_vec[k as usize]) == is_alpha_char(s@[k]),
            decreases n - j
        {
            lemma_exec_is_alpha_char(chars_vec[j as usize]);
            j += 1;
        }
        assert(forall|j: int| 0 <= j < n ==> exec_is_alpha_char(chars_vec[j as usize]) == is_alpha_char(s@[j]));

        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|k: int| 0 <= k < j ==> exec_is_lower_char(chars_vec[k as usize]) == is_lower_char(s@[k]),
            decreases n - j
        {
            lemma_exec_is_lower_char(chars_vec[j as usize]);
            j += 1;
        }
        assert(forall|j: int| 0 <= j < n ==> exec_is_lower_char(chars_vec[j as usize]) == is_lower_char(s@[j]));

        assert(has_cased == string_has_cased_char(s@));
        assert(all_lower == string_all_cased_are_lowercase(s@));
    }
    has_cased && all_lower
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn string_has_cased_char(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn string_all_cased_are_lowercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_lower_char(s[i])
}

fn islower(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i as int] == (string_has_cased_char(a[i]@) && string_all_cased_are_lowercase(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, but updating comment iteration number */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (string_has_cased_char(a[j]@) && string_all_cased_are_lowercase(a[j]@)),
        decreases a.len() - i
    {
        let s = a[i];
        let b = check_string(s);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}