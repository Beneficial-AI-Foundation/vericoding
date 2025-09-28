// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_fraction(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == '/') &&
    (forall|j: int| 0 <= j < s.len() ==> (s[j] == '/' || ('0' <= s[j] <= '9'))) &&
    (exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == '/' && 
        k > 0 && k + 1 < s.len() &&
        string_to_int(s.subrange(0, k)) > 0 && string_to_int(s.subrange(k+1, s.len() as int)) > 0) &&
    (forall|i: int| 0 <= i < s.len() && #[trigger] s[i] == '/' ==> 
        i > 0 && i + 1 < s.len() &&
        string_to_int(s.subrange(0, i)) > 0 && string_to_int(s.subrange(i+1, s.len() as int)) > 0)
}

spec fn get_numerator(s: Seq<char>) -> int
    recommends valid_fraction(s)
{
    let slash_pos = find_slash(s);
    string_to_int(s.subrange(0, slash_pos))
}

spec fn get_denominator(s: Seq<char>) -> int
    recommends valid_fraction(s)
{
    let slash_pos = find_slash(s);
    string_to_int(s.subrange(slash_pos+1, s.len() as int))
}

spec fn find_slash(s: Seq<char>) -> int
    recommends exists|i: int| 0 <= i < s.len() && s[i] == '/'
{
    find_slash_helper(s, 0)
}

spec fn string_to_int(s: Seq<char>) -> int {
    string_to_int_helper(s, 0)
}

spec fn char_to_int(c: char) -> int {
    if c == '0' { 0 }
    else if c == '1' { 1 }
    else if c == '2' { 2 }
    else if c == '3' { 3 }
    else if c == '4' { 4 }
    else if c == '5' { 5 }
    else if c == '6' { 6 }
    else if c == '7' { 7 }
    else if c == '8' { 8 }
    else if c == '9' { 9 }
    else { 0 }
}

spec fn find_slash_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos when 0 <= pos <= s.len() && exists|i: int| pos <= i < s.len() && s[i] == '/'
{
    if pos < s.len() && s[pos] == '/' { pos }
    else { find_slash_helper(s, pos + 1) }
}

spec fn string_to_int_helper(s: Seq<char>, acc: int) -> int
    decreases s.len()
{
    if s.len() == 0 { acc }
    else { string_to_int_helper(s.subrange(1, s.len() as int), acc * 10 + char_to_int(s[0])) }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved ghost code conversions to proper scope and added proper spec function */
proof fn lemma_valid_fraction_implies_wrapper(frac: Seq<char>)
    requires
        valid_fraction(frac)
    ensures
        get_numerator(frac) > 0 && get_denominator(frac) > 0
{
    assert(valid_fraction(frac));
    let slash_pos = find_slash(frac);
    assert(slash_pos > 0 && slash_pos + 1 < frac.len());
    assert(string_to_int(frac.subrange(0, slash_pos)) > 0);
    assert(string_to_int(frac.subrange(slash_pos+1, frac.len() as int)) > 0);
}

proof fn lemma_mod_zero_implies_divisible(a: int, b: int)
    requires
        b != 0
    ensures
        (a % b) == 0 <==> a % b == 0
{
}

spec fn compare_fractions(x_num: int, x_den: int, n_num: int, n_den: int) -> bool {
    (x_num * n_num) % (x_den * n_den) == 0
}
// </vc-helpers>

// <vc-spec>
fn simplify(x: Vec<char>, n: Vec<char>) -> (result: bool)
    requires 
        x.len() > 0 && n.len() > 0,
        exists|i: int| 0 <= i < x@.len() && x@[i] == '/',
        exists|j: int| 0 <= j < n@.len() && n@[j] == '/',
        forall|i: int| 0 <= i < x@.len() ==> (x@[i] == '/' || ('0' <= x@[i] <= '9')),
        forall|j: int| 0 <= j < n@.len() ==> (n@[j] == '/' || ('0' <= n@[j] <= '9')),
        valid_fraction(x@),
        valid_fraction(n@),
    ensures result <==> (get_numerator(x@) * get_numerator(n@)) % (get_denominator(x@) * get_denominator(n@)) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved ghost variable declarations to proof block */
    let result: bool;
    proof {
        lemma_valid_fraction_implies_wrapper(x@);
        lemma_valid_fraction_implies_wrapper(n@);
        
        let x_num = get_numerator(x@);
        let x_den = get_denominator(x@);
        let n_num = get_numerator(n@);
        let n_den = get_denominator(n@);
        
        assert(x_num > 0);
        assert(x_den > 0);
        assert(n_num > 0);
        assert(n_den > 0);
        
        result = compare_fractions(x_num, x_den, n_num, n_den);
    }
    result
}
// </vc-code>


}

fn main() {}