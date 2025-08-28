use vstd::prelude::*;


verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end
// pure-end

spec fn count_digits_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn count_digits_recursively_matches_implementation(text: Seq<char>, pos: int)
    requires
        0 <= pos <= text.len(),
    ensures
        count_digits_recursively(text.subrange(0, pos as int)) == pos - count_non_digits(text.subrange(0, pos as int)),
    decreases pos,
{
    if pos == 0 {
        assert(text.subrange(0, 0).len() == 0);
        assert(count_digits_recursively(text.subrange(0, 0)) == 0);
        assert(count_non_digits(text.subrange(0, 0)) == 0);
    } else {
        let sub_seq = text.subrange(0, (pos - 1) as int);
        count_digits_recursively_matches_implementation(text, pos - 1);
        assert(count_digits_recursively(sub_seq) == (pos - 1) - count_non_digits(sub_seq));
        if is_digit(text.index((pos - 1) as int)) {
            assert(count_digits_recursively(text.subrange(0, pos as int)) == count_digits_recursively(sub_seq) + 1);
            assert(count_non_digits(text.subrange(0, pos as int)) == count_non_digits(sub_seq));
        } else {
            assert(count_digits_recursively(text.subrange(0, pos as int)) == count_digits_recursively(sub_seq));
            assert(count_non_digits(text.subrange(0, pos as int)) == count_non_digits(sub_seq) + 1);
        }
    }
}

spec fn count_non_digits(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_non_digits(seq.drop_last()) + if !is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_digits(text: &Vec<char>) -> (count: usize)
    // pre-conditions-start
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
    // pre-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < text.len()
        invariant
            i <= text.len(),
            count <= i,
            count_digits_recursively(text@.subrange(0, i as int)) == count as int,
    {
        if is_digit(text@[i]) {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        count_digits_recursively_matches_implementation(text@, text.len() as int);
    }

    count
}
// </vc-code>

} // verus!

fn main() {}