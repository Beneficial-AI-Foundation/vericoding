// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
spec fn extend_with_char(s: Seq<char>, c: char, count: int) -> Seq<char> {
    if count == 0 {
        s
    } else {
        extend_with_char(s.push(c), c, count - 1)
    }
}

proof fn decode_rle_helper(lst: &Vec<(char, usize)>, index: int, decoded: Seq<char>)
    requires
        0 <= index <= lst.len(),
        decoded == decode_rle(lst.subrange(0, index as int)),
    ensures
        decode_rle(lst@) == extend_with_char(decoded, lst[index].0, lst[index].1 as int)
{ 
    if index < lst.len() {
        assert(lst@ == lst.subrange(0, index as int) + seq!(lst[index])) by {
            assert_equal(Seq::index_of(lst@, lst[index]) == index);
        }
        assert(decode_rle(lst@) == decode_rle(lst.subrange(0, index as int) + seq!(lst[index])));
        assert(decode_rle(lst.subrange(0, index as int) + seq!(lst[index])) == extend_with_char(decoded, lst[index].0, lst[index].1 as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        Vec::new()
    } else {
        let mut result = Vec::new();
        let mut current_char = s[0];
        let mut count = 1;
        
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                result.len() >= 0,
                forall|j: int| 0 <= j < result.len() ==> result[j].1 > 0,
                forall|j: int| 0 <= j < result.len() ==> j + 1 < result.len() ==> result[j].0 != result[j + 1].0,
                decode_rle(result@) == s.subrange(0, i),
                count > 0,
            decreases s.len() - i
        {
            if s[i] == current_char {
                count += 1;
            } else {
                result.push((current_char, count));
                current_char = s[i];
                count = 1;
            }
            i += 1;
        }
        result.push((current_char, count));
        result
    }
}
// </vc-code>

}
fn main() {}