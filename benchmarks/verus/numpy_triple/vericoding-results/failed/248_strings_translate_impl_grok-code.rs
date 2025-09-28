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
    /* code modified by LLM (iteration 5): fixed type mismatches by using ghost sequences in specifications and casting usize to int for comparisons */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() as int == i as int,
            forall |j: int| 0 <= j < i ==> result[j].len() <= a[j].len()
    {
        let mut current_result: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < a[i].len()
            invariant
                current_result@.len() == k as int,
                forall |idx: int| 0 <= idx < current_result@.len() ==> {
                    exists |orig_char: u8, table_idx: int| 
                        0 <= table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        a[i]@[idx] == orig_char &&
                        (forall |j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) &&
                        current_result@[idx] == table@[table_idx]
                }
        {
            let orig_char = a[i][k];
            if !deletechars.contains(&orig_char) {
                let translated = table[orig_char as usize];
                current_result.push(translated);
            }
            k += 1;
        }
        result.push(current_result);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}