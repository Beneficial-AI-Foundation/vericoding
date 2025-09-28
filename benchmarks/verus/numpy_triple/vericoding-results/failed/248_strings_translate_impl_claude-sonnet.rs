// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_char_to_delete(c: u8, deletechars: &Vec<u8>) -> (result: bool)
    ensures
        result == exists|j: int| 0 <= j < deletechars.len() && c == deletechars[j],
{
    let mut i = 0;
    while i < deletechars.len()
        invariant
            0 <= i <= deletechars.len(),
            forall|j: int| 0 <= j < i ==> c != deletechars[j],
        decreases deletechars.len() - i
    {
        if c == deletechars[i] {
            return true;
        }
        i = i + 1;
    }
    false
}

fn translate_char(c: u8, table: &Vec<u8>) -> (result: u8)
    requires
        table.len() == 256,
    ensures
        result == table[c as int],
{
    table[c as usize]
}

/* helper modified by LLM (iteration 5): strengthened postconditions to satisfy translate_string requirements */
fn translate_string(s: &Vec<u8>, table: &Vec<u8>, deletechars: &Vec<u8>) -> (result: Vec<u8>)
    requires
        table.len() == 256,
    ensures
        result.len() <= s.len(),
        forall|c: u8| #[trigger] result@.contains(c) ==> {
            forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
        },
        forall|k: int| 0 <= k < result.len() ==> {
            exists|orig_char: u8, table_idx: int|
                0 <= table_idx < 256 &&
                orig_char == table_idx as u8 &&
                result[k] == table[table_idx as int] &&
                s@.contains(orig_char) &&
                (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
        },
        forall|orig_char: u8| #[trigger] s@.contains(orig_char) ==> {
            (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                exists|translated_char: u8| result@.contains(translated_char) &&
                    exists|table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char as int == table_idx &&
                        translated_char == table[table_idx as int]
            }
        },
        deletechars.len() == 0 ==> {
            result.len() == s.len() &&
            forall|k: int| 0 <= k < s.len() ==> {
                exists|table_idx: int|
                    0 <= table_idx < 256 &&
                    s[k] as int == table_idx &&
                    result[k] == table[table_idx as int]
            }
        },
        s.len() == 0 ==> result.len() == 0,
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() <= i,
            forall|c: u8| #[trigger] result@.contains(c) ==> {
                forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
            },
            forall|k: int| 0 <= k < result.len() ==> {
                exists|orig_char: u8, table_idx: int|
                    0 <= table_idx < 256 &&
                    orig_char == table_idx as u8 &&
                    result[k] == table[table_idx as int] &&
                    s@.subrange(0, i as int).contains(orig_char) &&
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
            },
            forall|orig_char: u8| #[trigger] s@.subrange(0, i as int).contains(orig_char) ==> {
                (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                    exists|translated_char: u8| result@.contains(translated_char) &&
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            orig_char as int == table_idx &&
                            translated_char == table[table_idx as int]
                }
            },
            deletechars.len() == 0 ==> result.len() == i,
        decreases s.len() - i
    {
        let current_char = s[i];
        if !is_char_to_delete(current_char, deletechars) {
            let translated = translate_char(current_char, table);
            result.push(translated);
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
    /* code modified by LLM (iteration 5): fixed precondition violations and strengthened invariants */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                result[j].len() <= a[j].len() &&
                (forall|c: u8| #[trigger] result[j]@.contains(c) ==> {
                    forall|k: int| 0 <= k < deletechars.len() ==> c != deletechars[k]
                }) &&
                (forall|k: int| 0 <= k < result[j].len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        result[j][k] == table[table_idx as int] &&
                        a[j]@.contains(orig_char) &&
                        (forall|l: int| 0 <= l < deletechars.len() ==> orig_char != deletechars[l])
                }) &&
                (forall|orig_char: u8| #[trigger] a[j]@.contains(orig_char) ==> {
                    (forall|k: int| 0 <= k < deletechars.len() ==> orig_char != deletechars[k]) ==> {
                        exists|translated_char: u8| result[j]@.contains(translated_char) &&
                            exists|table_idx: int|
                                0 <= table_idx < 256 &&
                                orig_char as int == table_idx &&
                                translated_char == table[table_idx as int]
                    }
                }) &&
                (deletechars.len() == 0 ==> {
                    result[j].len() == a[j].len() &&
                    (forall|k: int| 0 <= k < a[j].len() ==> {
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            a[j][k] as int == table_idx &&
                            result[j][k] == table[table_idx as int]
                    })
                }) &&
                (a[j].len() == 0 ==> result[j].len() == 0)
            },
        decreases a.len() - i
    {
        let translated_string = translate_string(&a[i], &table, &deletechars);
        result.push(translated_string);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}