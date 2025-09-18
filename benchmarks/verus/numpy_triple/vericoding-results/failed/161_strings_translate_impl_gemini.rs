// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec and loop invariants to prove length property */
fn translate_vec(a_vec: &Vec<u8>, table: &Vec<u8>, deletechars: &Vec<u8>) -> (res: Vec<u8>)
    requires
        table.len() == 256,
    ensures
        res.len() <= a_vec.len(),
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < a_vec.len()
        invariant
            i <= a_vec.len(),
            res.len() <= i
        decreases a_vec.len() - i
    {
        let c = a_vec[i];
        let mut found_in_delete = false;
        let mut j: usize = 0;
        while j < deletechars.len()
            invariant
                j <= deletechars.len()
            decreases deletechars.len() - j
        {
            if deletechars[j] == c {
                found_in_delete = true;
                break;
            }
            j = j + 1;
        }

        if !found_in_delete {
            let translated_char = table[c as usize];
            res.push(translated_char);
        }

        i = i + 1;
    }
    res
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
/* code modified by LLM (iteration 2): fixed compilation errors by removing incorrect old() usage */
{
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            table.len() == 256,
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result[j].len() <= a@[j].len()
        decreases a.len() - i
    {
        let translated_sub_vec = translate_vec(&a[i], &table, &deletechars);
        result.push(translated_sub_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}