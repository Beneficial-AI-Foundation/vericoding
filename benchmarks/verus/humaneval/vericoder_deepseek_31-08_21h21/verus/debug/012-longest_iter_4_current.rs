use vstd::prelude::*;

verus! {

spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, result: Option<&Vec<u8>>) -> (result: bool) {
    match result {
        None => strings.len() == 0,
        Some(s) => {
            (forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len())
                && (exists|i: int|
                #![auto]
                (0 <= i < strings.len() && s == strings[i] && (forall|j: int|
                    #![auto]
                    0 <= j < i ==> strings[j].len() < s.len())))
        },
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_vec_len_nonnegative<T>(v: &Vec<T>)
    ensures
        v.len() >= 0,
{
}

spec fn is_max_length(strings: &Vec<Vec<u8>>, index: int, length: int) -> bool {
    &&& 0 <= index < strings.len()
    &&& strings[index].len() as int == length
    &&& (forall|j: int| 0 <= j < strings.len() ==> strings[j].len() as int <= length)
}

spec fn has_max_length_string(strings: &Vec<Vec<u8>>) -> bool {
    exists|i: int| is_max_length(strings, i, max_length(strings))
}

spec fn max_length(strings: &Vec<Vec<u8>>) -> int {
    if strings.len() == 0 {
        0
    } else {
        let mut max: int = 0;
        let mut j: int = 0;
        while j < strings.len() {
            if strings[j].len() as int > max {
                max = strings[j].len() as int;
            }
            j = j + 1;
        }
        max
    }
}

proof fn max_length_exists_for_nonempty_vecs(strings: &Vec<Vec<u8>>)
    requires
        strings.len() > 0,
    ensures
        exists|i: int| 0 <= i < strings.len() && strings[i].len() as int == max_length(strings),
{
}

proof fn max_length_properties(strings: &Vec<Vec<u8>>)
    ensures
        (forall|i: int| 0 <= i < strings.len() ==> strings[i].len() as int <= max_length(strings)),
        strings.len() == 0 ==> max_length(strings) == 0,
{
}

proof fn lemma_vec_len_cast<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v[i as usize].len() as int == v[i as usize].len(),
{
}
// </vc-helpers>

// <vc-spec>
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    // post-conditions-start
    ensures
        expr_inner_longest(strings, result),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if strings.is_empty() {
        max_length_properties(strings);
        None
    } else {
        max_length_properties(strings);
        let mut max_len: int = 0;
        let mut result_index: Option<int> = None;
        let mut i: int = 0;
        while i < strings.len() as int
            invariant
                i <= strings.len() as int,
                max_len == (if result_index.is_some() { strings[result_index.unwrap() as usize].len() as int } else { 0 }),
                forall|j: int| 0 <= j < i ==> strings[j as usize].len() as int <= max_len,
                result_index.is_some() ==> (
                    0 <= result_index.unwrap() < i && strings[result_index.unwrap() as usize].len() as int == max_len
                    && forall|j: int| 0 <= j < result_index.unwrap() ==> strings[j as usize].len() as int < max_len
                ),
        {
            lemma_vec_len_cast(strings, i);
            if strings[i as usize].len() as int > max_len {
                max_len = strings[i as usize].len() as int;
                result_index = Some(i);
            } else if strings[i as usize].len() as int == max_len && result_index.is_none() {
                result_index = Some(i);
            }
            i = i + 1;
        }
        match result_index {
            Some(idx) => Some(&strings[idx as usize]),
            None => None,
        }
    }
}
// </vc-code>

fn main() {}
}