// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, n: int) -> bool {
  0 <= n <= 26
}

spec fn get_comparison_char(n: int) -> char {
  if n == 0 { 'a' }
  else if n == 1 { 'b' }
  else if n == 2 { 'c' }
  else if n == 3 { 'd' }
  else if n == 4 { 'e' }
  else if n == 5 { 'f' }
  else if n == 6 { 'g' }
  else if n == 7 { 'h' }
  else if n == 8 { 'i' }
  else if n == 9 { 'j' }
  else if n == 10 { 'k' }
  else if n == 11 { 'l' }
  else if n == 12 { 'm' }
  else if n == 13 { 'n' }
  else if n == 14 { 'o' }
  else if n == 15 { 'p' }
  else if n == 16 { 'q' }
  else if n == 17 { 'r' }
  else if n == 18 { 's' }
  else if n == 19 { 't' }
  else if n == 20 { 'u' }
  else if n == 21 { 'v' }
  else if n == 22 { 'w' }
  else if n == 23 { 'x' }
  else if n == 24 { 'y' }
  else if n == 25 { 'z' }
  else { '|' }
}

spec fn is_lowercase(c: char) -> bool {
  'a' <= c && c <= 'z'
}

spec fn is_uppercase(c: char) -> bool {
  'A' <= c && c <= 'Z'
}

spec fn to_lowercase(c: char) -> char {
  if is_uppercase(c) {
    ((c as u8) - ('A' as u8) + ('a' as u8)) as char
  } else {
    c
  }
}

spec fn to_uppercase(c: char) -> char {
  if is_lowercase(c) {
    ((c as u8) - ('a' as u8) + ('A' as u8)) as char
  } else {
    c
  }
}

spec fn transform_string(s: Seq<char>, n: int) -> Seq<char> {
  let comp_char = get_comparison_char(n);
  transform_with_comp_char(to_lowercase_string(s), comp_char)
}

spec fn to_lowercase_string(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else {
    s.subrange(0, 1).map(|_i: int, c: char| to_lowercase(c)) + to_lowercase_string(s.skip(1))
  }
}

spec fn transform_with_comp_char(s: Seq<char>, comp_char: char) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else if s[0] < comp_char {
    s.subrange(0, 1).map(|_i: int, c: char| to_uppercase(c)) + transform_with_comp_char(s.skip(1), comp_char)
  } else {
    s.subrange(0, 1) + transform_with_comp_char(s.skip(1), comp_char)
  }
}
// </vc-preamble>

// <vc-helpers>
spec fn char_transform(c: char, comp: char) -> char {
    let lc = to_lowercase(c);
    if lc < comp { to_uppercase(lc) } else { lc }
}

spec fn pointwise_transform(s: Seq<char>, comp: char) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else {
        s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp)
    }
}

proof fn lemma_pointwise_len(s: Seq<char>, comp: char)
    ensures
        pointwise_transform(s, comp).len() == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
        assert(pointwise_transform(s, comp) == s);
    } else {
        lemma_pointwise_len(s.skip(1), comp);
        assert(s.subrange(0, 1).len() == 1);
        assert(pointwise_transform(s, comp) == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp));
        assert((s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp)).len() == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)).len() + pointwise_transform(s.skip(1), comp).len());
        assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)).len() == 1);
        assert(s.len() == 1 + s.skip(1).len());
    }
}

proof fn lemma_pointwise_index(s: Seq<char>, comp: char, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        pointwise_transform(s, comp)[i] == char_transform(s[i], comp),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        if i == 0 {
            assert(pointwise_transform(s, comp) == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp));
            assert(s.subrange(0, 1).len() == 1);
            assert((s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp))[0] == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp))[0]);
            assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp))[0] == char_transform(s[0], comp));
        } else {
            lemma_pointwise_index(s.skip(1), comp, i - 1);
            assert(s.subrange(0, 1).len() == 1);
            assert(pointwise_transform(s, comp) == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp));
            assert((s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp))[i] == pointwise_transform(s.skip(1), comp)[i - 1]);
            assert(s[i] == s.skip(1)[i - 1]);
        }
    }
}

proof fn lemma_transform_eq_pointwise(s: Seq<char>, comp: char)
    ensures
        transform_with_comp_char(to_lowercase_string(s), comp) == pointwise_transform(s, comp),
    decreases s.len()
{
    if s.len() == 0 {
        assert(to_lowercase_string(s) == s);
        assert(transform_with_comp_char(s, comp) == s);
        assert(pointwise_transform(s, comp) == s);
    } else {
        lemma_transform_eq_pointwise(s.skip(1), comp);
        let head_l = s.subrange(0, 1).map(|_i: int, c: char| to_lowercase(c));
        let tail_l = to_lowercase_string(s.skip(1));
        assert(to_lowercase_string(s) == head_l + tail_l);
        assert(head_l.len() == 1);
        let lc0 = to_lowercase(s[0]);
        if lc0 < comp {
            assert(transform_with_comp_char(to_lowercase_string(s), comp) == head_l.map(|_i: int, c: char| to_uppercase(c)) + transform_with_comp_char(tail_l, comp));
            assert(head_l.map(|_i: int, c: char| to_uppercase(c))[0] == to_uppercase(lc0));
            assert(pointwise_transform(s, comp) == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp));
            assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp))[0] == char_transform(s[0], comp));
            assert(char_transform(s[0], comp) == to_uppercase(lc0));
            assert(head_l.map(|_i: int, c: char| to_uppercase(c)) == Seq::singleton(to_uppercase(lc0)));
            assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) == Seq::singleton(to_uppercase(lc0)));
            assert(transform_with_comp_char(tail_l, comp) == pointwise_transform(s.skip(1), comp));
        } else {
            assert(transform_with_comp_char(to_lowercase_string(s), comp) == head_l + transform_with_comp_char(tail_l, comp));
            assert(pointwise_transform(s, comp) == s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) + pointwise_transform(s.skip(1), comp));
            assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp))[0] == char_transform(s[0], comp));
            assert(char_transform(s[0], comp) == lc0);
            assert(head_l == Seq::singleton(lc0));
            assert(s.subrange(0, 1).map(|_i: int, c: char| char_transform(c, comp)) == Seq::singleton(lc0));
            assert(transform_with_comp_char(tail_l, comp) == pointwise_transform(s.skip(1), comp));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, n: i8) -> (result: Vec<char>)
  requires valid_input(s@, n as int)
  ensures result@ == transform_string(s@, n as int)
// </vc-spec>
// <vc-code>
{
    let comp = get_comparison_char(n as int);
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> out@[k] == char_transform(s@[k], comp),
        decreases (s.len() - i) as int
    {
        let c = s[i];
        let lc = to_lowercase(c);
        let r = if lc < comp { to_uppercase(lc) } else { lc };
        out.push(r);
        i = i + 1;
    }
    proof {
        assert(i == s.len());
        lemma_pointwise_len(s@, comp);
        assert(out@.len() == s@.len());
        assert(forall |k: int| 0 <= k < s@.len() ==> out@[k] == pointwise_transform(s@, comp)[k]) by {
            assert forall |k: int| 0 <= k < s@.len() implies out@[k] == pointwise_transform(s@, comp)[k] by {
                if 0 <= k && k < s@.len() {
                    assert(k < i as int);
                    assert(out@[k] == char_transform(s@[k], comp));
                    lemma_pointwise_index(s@, comp, k);
                    assert(pointwise_transform(s@, comp)[k] == char_transform(s@[k], comp));
                }
            }
        }
        assert(out@ == pointwise_transform(s@, comp));
        lemma_transform_eq_pointwise(s@, comp);
        assert(pointwise_transform(s@, comp) == transform_with_comp_char(to_lowercase_string(s@), comp));
        assert(out@ == transform_string(s@, n as int));
    }
    out
}
// </vc-code>


}

fn main() {}