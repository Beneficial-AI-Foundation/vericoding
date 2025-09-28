// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): added decreases clause to outer while loop */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> {
                result[idx].len() <= a[idx].len() &&
                (forall|c: u8| #[trigger] result[idx]@.contains(c) ==> {
                    forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
                }) &&
                (forall|k: int| 0 <= k < result[idx].len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        #[trigger] result[idx][k] == table[table_idx as int] &&
                        a[idx]@.contains(orig_char) &&
                        (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
                }) &&
                (forall|orig_char: u8| #[trigger] a[idx]@.contains(orig_char) ==> {
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                        exists|translated_char: u8| result[idx]@.contains(translated_char) &&
                            exists|table_idx: int|
                                0 <= table_idx < 256 &&
                                orig_char as int == table_idx &&
                                translated_char == table[table_idx as int]
                    }
                }) &&
                (deletechars.len() == 0 ==> {
                    result[idx].len() == a[idx].len() &&
                    (forall|k: int| 0 <= k < a[idx].len() ==> {
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            a[idx][k] as int == table_idx &&
                            #[trigger] result[idx][k] == table[table_idx as int]
                    })
                }) &&
                (a[idx].len() == 0 ==> result[idx].len() == 0)
            },
        decreases a.len() - i
    {
        let mut translated: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < a[i].len()
            invariant
                0 <= j <= a[i as int].len(),
                translated.len() <= j,
                forall|c: u8| #[trigger] translated@.contains(c) ==> {
                    forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> c != deletechars[del_idx]
                },
                forall|k: int| 0 <= k < translated.len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        #[trigger] translated[k] == table[table_idx as int] &&
                        a[i as int]@.contains(orig_char) &&
                        (forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> orig_char != deletechars[del_idx])
                },
                forall|orig_idx: int| 0 <= orig_idx < j ==> {
                    let orig_char = a[i as int][orig_idx];
                    (forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> orig_char != deletechars[del_idx]) ==> {
                        exists|translated_char: u8| translated@.contains(translated_char) &&
                            exists|table_idx: int|
                                0 <= table_idx < 256 &&
                                orig_char as int == table_idx &&
                                translated_char == table[table_idx as int]
                    }
                },
                deletechars.len() == 0 ==> translated.len() == j,
                deletechars.len() == 0 ==> forall|k: int| 0 <= k < j ==> {
                    exists|table_idx: int|
                        0 <= table_idx < 256 &&
                        a[i as int][k] as int == table_idx &&
                        #[trigger] translated[k] == table[table_idx as int]
                },
            decreases a[i as int].len() - j
        {
            let orig_char = a[i][j];
            let mut is_deleted = false;
            let mut del_idx: usize = 0;
            while del_idx < deletechars.len()
                invariant
                    0 <= del_idx <= deletechars.len(),
                    is_deleted == exists|k: int| 0 <= k < del_idx && deletechars[k] == orig_char,
                decreases deletechars.len() - del_idx
            {
                if deletechars[del_idx] == orig_char {
                    is_deleted = true;
                }
                del_idx = del_idx + 1;
            }
            
            if !is_deleted {
                let table_idx = orig_char as usize;
                let translated_char = table[table_idx];
                translated.push(translated_char);
            }
            j = j + 1;
        }
        result.push(translated);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}