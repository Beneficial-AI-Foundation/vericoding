// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed subseq syntax error */
spec fn is_in_deletechars(c: u8, deletechars: &Vec<u8>) -> bool {
    exists|j: int| 0 <= j < deletechars.len() && deletechars[j] == c
}

fn translate_string(s: &Vec<u8>, table: &Vec<u8>, deletechars: &Vec<u8>) -> (result: Vec<u8>)
    requires
        table.len() == 256,
    ensures
        result.len() <= s.len(),
        forall|c: u8| #[trigger] result@.contains(c) ==> !is_in_deletechars(c, deletechars),
        forall|k: int| 0 <= k < result.len() ==> {
            exists|orig_char: u8, table_idx: int|
                0 <= table_idx < 256 &&
                orig_char == table_idx as u8 &&
                result[k] == table[table_idx as int] &&
                s@.contains(orig_char) &&
                !is_in_deletechars(orig_char, deletechars)
        },
        forall|orig_char: u8| #[trigger] s@.contains(orig_char) ==> {
            !is_in_deletechars(orig_char, deletechars) ==> {
                exists|translated_char: u8| result@.contains(translated_char) &&
                    translated_char == table[orig_char as int]
            }
        },
        deletechars.len() == 0 ==> {
            result.len() == s.len() &&
            forall|k: int| 0 <= k < s.len() ==> result[k] == table[s[k] as int]
        },
        s.len() == 0 ==> result.len() == 0,
{
    let mut result: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            table.len() == 256,
            0 <= i <= s.len(),
            result.len() <= i,
            forall|c: u8| #[trigger] result@.contains(c) ==> !is_in_deletechars(c, deletechars),
            forall|k: int| 0 <= k < result.len() ==> {
                exists|orig_char: u8, table_idx: int|
                    0 <= table_idx < 256 &&
                    orig_char == table_idx as u8 &&
                    result[k] == table[table_idx as int] &&
                    s@.contains(orig_char) &&
                    !is_in_deletechars(orig_char, deletechars)
            },
            forall|orig_char: u8| #[trigger] s@.subrange(0, i as int).contains(orig_char) ==> {
                !is_in_deletechars(orig_char, deletechars) ==> {
                    exists|translated_char: u8| result@.contains(translated_char) &&
                        translated_char == table[orig_char as int]
                }
            },
        decreases s.len() - i,
    {
        let c = s[i];
        let mut is_deleted = false;
        let mut j = 0;
        while j < deletechars.len()
            invariant
                0 <= j <= deletechars.len(),
                is_deleted <==> exists|k: int| 0 <= k < j && deletechars[k] == c,
            decreases deletechars.len() - j,
        {
            if deletechars[j] == c {
                is_deleted = true;
            }
            j = j + 1;
        }
        assert(is_deleted <==> is_in_deletechars(c, deletechars));
        
        if !is_deleted {
            let translated = table[c as usize];
            result.push(translated);
            assert(result[result.len() - 1] == table[c as int]);
        }
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn translate(a: Vec<Vec<u8>>, table: Vec<u8>, deletechars: Vec<u8>) -> (result: Vec<Vec<u8>>)
    requires
        table.len() == 256,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {

            result[i].len() <= a[i].len() &&

            (forall|c: u8| #[trigger] result[i]@.contains(c) ==> {
                forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
            }) &&

            (forall|k: int| 0 <= k < result[i].len() ==> {
                exists|orig_char: u8, table_idx: int|
                    0 <= table_idx < 256 &&
                    orig_char == table_idx as u8 &&
                    #[trigger] result[i][k] == table[table_idx as int] &&

                    a[i]@.contains(orig_char) &&
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
            }) &&

            (forall|orig_char: u8| #[trigger] a[i]@.contains(orig_char) ==> {
                (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                    exists|translated_char: u8| result[i]@.contains(translated_char) &&
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            orig_char as int == table_idx &&
                            translated_char == table[table_idx as int]
                }
            }) &&

            (deletechars.len() == 0 ==> {
                result[i].len() == a[i].len() &&
                (forall|k: int| 0 <= k < a[i].len() ==> {
                    exists|table_idx: int|
                        0 <= table_idx < 256 &&
                        a[i][k] as int == table_idx &&
                        #[trigger] result[i][k] == table[table_idx as int]
                })
            }) &&

            (a[i].len() == 0 ==> result[i].len() == 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants to satisfy postconditions */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            table.len() == 256,
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> {
                result[k].len() <= a[k].len() &&
                (forall|c: u8| #[trigger] result[k]@.contains(c) ==> {
                    forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
                }) &&
                (forall|m: int| 0 <= m < result[k].len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        result[k][m] == table[table_idx as int] &&
                        a[k]@.contains(orig_char) &&
                        (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
                }) &&
                (forall|orig_char: u8| #[trigger] a[k]@.contains(orig_char) ==> {
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                        exists|translated_char: u8| result[k]@.contains(translated_char) &&
                            translated_char == table[orig_char as int]
                    }
                }) &&
                (deletechars.len() == 0 ==> {
                    result[k].len() == a[k].len() &&
                    forall|m: int| 0 <= m < a[k].len() ==> result[k][m] == table[a[k][m] as int]
                }) &&
                (a[k].len() == 0 ==> result[k].len() == 0)
            },
        decreases a.len() - i,
    {
        let translated = translate_string(&a[i], &table, &deletechars);
        result.push(translated);
        assert(result.len() == i + 1);
        assert(result[i as int] == translated);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}