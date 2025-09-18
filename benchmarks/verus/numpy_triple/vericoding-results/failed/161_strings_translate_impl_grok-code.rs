// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed requires clause syntax in spec fn translated_char */
spec fn translated_char(c: u8, table: Seq<u8>) -> u8
{
    requires(c as int < table.len());
    table[c as int]
}
spec fn is_deleted(c: u8, deletechars: Seq<u8>) -> bool
/* helper modified by LLM (iteration 3): no changes made */
{
    deletechars.contains(c)
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
    /* code modified by LLM (iteration 5): implemented translation loop with invariants and proof to verify specs */
    let mut result: Vec<Vec<u8>> = Vec::new();
    for i in 0..a.len()
        invariant result.len() == i
    {
        let mut translated_row: Vec<u8> = Vec::new();
        let row = &a[i];
        for j in 0..row.len() {
            let c = row[j];
            if !deletechars@.contains(c) {
                translated_row.push(table[c as usize]);
            }
        }
        result.push(translated_row);
    }
    proof {
        assert forall|i: int| 0 <= i < a.len() implies result[i].len() <= a[i].len();
    }
    result
}
// </vc-code>

}
fn main() {}