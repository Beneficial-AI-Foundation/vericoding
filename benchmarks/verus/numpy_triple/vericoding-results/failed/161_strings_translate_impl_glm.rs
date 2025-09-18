// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by replacing invariant_except_break with invariant */
fn char_in_deletechars(c: u8, deletechars: &Vec<u8>) -> (found: bool)
    ensures found == exists|i: int| 0 <= i < deletechars.len() && deletechars[i] == c
{
    let mut found = false;
    let mut i = 0;
    while i < deletechars.len()
        invariant 0 <= i <= deletechars.len(),
        invariant(!found ==> forall|j: int| 0 <= j < i ==> deletechars[j] != c),
        invariant found ==> exists|j: int| 0 <= j <= i && deletechars[j] == c
    {
        if deletechars[i] == c {
            found = true;
            break;
        }
        i += 1;
    }
    found
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
    /* code modified by LLM (iteration 5): no changes */
    let mut result: Vec<Vec<u8>> = Vec::new();
    for i in 0..a.len()
        invariant result.len() == i
    {
        let row = &a[i];
        let mut translated_row: Vec<u8> = Vec::new();
        for j in 0..row.len()
            invariant translated_row.len() <= j
        {
            let c = row[j];
            let should_delete = char_in_deletechars(c, &deletechars);
            if !should_delete {
                assert(c as usize < table.len());
                let translated_c = table[c as usize];
                translated_row.push(translated_c);
            }
        }
        result.push(translated_row);
    }
    result
}
// </vc-code>

}
fn main() {}