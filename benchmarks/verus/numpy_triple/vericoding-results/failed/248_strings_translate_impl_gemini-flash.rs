// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper function as not needed */
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
/* code modified by LLM (iteration 5): fixed sequence subsequence call */
{
    let mut result_vec: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            // All properties must hold for the already processed elements
            forall|k: int| 0 <= k < i ==> {
                result_vec[k].len() <= a[k].len() &&
                (forall|c: u8| #[trigger] result_vec[k]@.contains(c) ==> {
                    forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
                }) &&
                (forall|idx: int| 0 <= idx < result_vec[k].len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        #[trigger] result_vec[k][idx] == table[table_idx as int] &&
                        a[k]@.contains(orig_char) &&
                        (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
                }) &&

                (forall|orig_char: u8| #[trigger] a[k]@.contains(orig_char) ==> {
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                        exists|translated_char: u8| result_vec[k]@.contains(translated_char) &&
                            exists|table_idx: int|
                                0 <= table_idx < 256 &&
                                orig_char as int == table_idx &&
                                translated_char == table[table_idx as int]
                    }
                }) &&

                (deletechars.len() == 0 ==> {
                    result_vec[k].len() == a[k].len() &&
                    (forall|idx: int| 0 <= idx < a[k].len() ==> {
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            a[k][idx] as int == table_idx &&
                            #[trigger] result_vec[k][idx] == table[table_idx as int]
                    })
                }) &&
                (a[k].len() == 0 ==> result_vec[k].len() == 0)
            }
        decreases a.len() - i
    {
        let inner_vec = &a[i];
        let mut translated_inner_vec = Vec::new();
        let mut j = 0;
        while j < inner_vec.len()
            invariant
                0 <= j <= inner_vec.len(),
                translated_inner_vec.len() <= j,
                forall|c: u8| #[trigger] translated_inner_vec@.contains(c) ==> {
                    forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> c != deletechars[del_idx]
                },
                forall|idx: int| 0 <= idx < translated_inner_vec.len() ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        #[trigger] translated_inner_vec[idx] == table[table_idx as int] &&
                        inner_vec@.contains(orig_char) &&
                        (forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> orig_char != deletechars[del_idx])
                },
                forall|orig_char: u8| #![trigger] (inner_vec@.subsequence(0, j)@.contains(orig_char) && (forall|del_idx: int| 0 <= del_idx < deletechars.len() ==> orig_char != deletechars[del_idx])) ==> {
                    exists|translated_char: u8| translated_inner_vec@.contains(translated_char)
                        && exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            orig_char as int == table_idx &&
                            translated_char == table[table_idx as int]
                },
                (deletechars.len() == 0 ==> {
                    translated_inner_vec.len() == j &&
                    (forall|idx: int| 0 <= idx < j ==> {
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            #[trigger] inner_vec[idx] as int == table_idx &&
                            translated_inner_vec[idx] == table[table_idx as int]
                    })
                })
            decreases inner_vec.len() - j
        {
            let original_char = inner_vec[j];
            let mut should_delete = false;
            let mut k = 0;
            while k < deletechars.len()
                invariant
                    0 <= k <= deletechars.len(),
                    !should_delete ==> forall|_k: int| 0 <= _k < k ==> original_char != deletechars[_k]
                decreases deletechars.len() - k
            {
                if original_char == deletechars[k] {
                    should_delete = true;
                }
                k = k + 1;
            }

            if !should_delete {
                let translated_char = table[original_char as usize]; // Modified: original_char as usize
                translated_inner_vec.push(translated_char);
            }
            j = j + 1;
        }
        result_vec.push(translated_inner_vec);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}