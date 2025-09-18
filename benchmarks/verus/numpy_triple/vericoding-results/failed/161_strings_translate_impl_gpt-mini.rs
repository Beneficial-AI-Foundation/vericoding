// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for checking that a byte is not in deletechars */
spec fn not_in_deletechars(c: u8, deletechars: Vec<u8>) -> bool { forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j] }
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
    /* code modified by LLM (iteration 5): implement translate by filtering deletechars and mapping via table */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: int = 0;
    while i < a.len() {
        invariant 0 <= i && i <= a.len() && result.len() == i;
        decreases a.len() - i;

        let mut row: Vec<u8> = Vec::new();
        let mut k: int = 0;
        while k < a[i].len() {
            invariant 0 <= k && k <= a[i].len() && row.len() <= a[i].len();
            decreases a[i].len() - k;

            let mut m: int = 0;
            let mut is_del: bool = false;
            while m < deletechars.len() {
                invariant 0 <= m && m <= deletechars.len();
                invariant is_del ==> exists|q: int| 0 <= q < m && deletechars[q] == a[i][k];
                invariant (!is_del) ==> forall|q: int| 0 <= q < m ==> deletechars[q] != a[i][k];
                decreases deletechars.len() - m;
                if deletechars[m] == a[i][k] {
                    is_del = true;
                }
                m = m + 1;
            }

            if !is_del {
                proof {
                    assert(a[i][k] as int >= 0 && a[i][k] as int < 256);
                }
                row.push(table[a[i][k] as int]);
            }

            k = k + 1;
        }

        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}