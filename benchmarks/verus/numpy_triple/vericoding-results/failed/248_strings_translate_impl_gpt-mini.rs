// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec conversion from byte to int */
spec fn byte_to_index(b: u8) -> (r: int)
    ensures
        0 <= r,
        r < 256,
{
    b as int
}

/* helper modified by LLM (iteration 5): runtime table lookup with spec-level ensures using table@ */
fn table_lookup(table: Vec<u8>, b: u8) -> (r: u8)
    requires
        table.len() == 256,
    ensures
        r == table@[b as int],
{
    table[b as usize]
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
    /* code modified by LLM (iteration 5): use spec-level indexing table@ and seq @-indexing in invariants to avoid usize/int mismatches */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            result.len() == i,
            forall|idx: int| 0 <= idx && idx < i as int ==> {
                result@[idx].len() as int <= a@[idx].len() as int &&
                (forall|k: int| 0 <= k && k < result@[idx].len() as int ==> {
                    exists|orig_char: u8, table_idx: int|
                        0 <= table_idx && table_idx < 256 &&
                        orig_char == table_idx as u8 &&
                        #[trigger] (result@[idx])@[k] == table@[table_idx] &&
                        (a@[idx])@.contains(orig_char) &&
                        (forall|j: int| 0 <= j && j < deletechars.len() ==> orig_char != deletechars@[j])
                }) &&
                (forall|orig_char: u8| #[trigger] (a@[idx])@.contains(orig_char) ==> {
                    (forall|j: int| 0 <= j && j < deletechars.len() ==> orig_char != deletechars@[j]) ==> {
                        exists|translated_char: u8| (result@[idx])@.contains(translated_char) &&
                            exists|table_idx: int|
                                0 <= table_idx && table_idx < 256 &&
                                orig_char as int == table_idx &&
                                translated_char == table@[table_idx]
                    }
                }) &&
                (deletechars.len() == 0 ==> {
                    result@[idx].len() as int == a@[idx].len() as int &&
                    (forall|k: int| 0 <= k && k < a@[idx].len() as int ==> {
                        exists|table_idx: int|
                            0 <= table_idx && table_idx < 256 &&
                            (a@[idx])@[k] as int == table_idx &&
                            #[trigger] (result@[idx])@[k] == table@[table_idx]
                    })
                }) &&
                (a@[idx].len() == 0 ==> result@[idx].len() == 0)
            },
        decreases a.len() as int - i as int
    {
        let mut row: Vec<u8> = Vec::new();
        let mut origs: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < a[i].len()
            invariant
                0 <= k as int,
                k as int <= a[i].len() as int,
                row.len() == origs.len(),
                forall|t: int| 0 <= t && t < row.len() as int ==> (row@[t] == table@[origs@[t] as int] && (a@[i])@.contains(origs@[t]) && (forall|j: int| 0 <= j && j < deletechars.len() ==> origs@[t] != deletechars@[j])),
                forall|p: int| 0 <= p && p < k as int ==> ((forall|j: int| 0 <= j && j < deletechars.len() ==> (a@[i])@[p] != deletechars@[j]) ==> exists|t: int| 0 <= t && t < row.len() as int && origs@[t] == (a@[i])@[p]),
            decreases a[i].len() as int - k as int
        {
            let c = a[i][k];
            let mut is_del: bool = false;
            let mut j: usize = 0;
            while j < deletechars.len()
                invariant
                    0 <= j as int,
                    j as int <= deletechars.len() as int,
                    (is_del ==> exists|jj: int| 0 <= jj && jj < j as int && deletechars[jj] == c),
                decreases deletechars.len() as int - j as int
            {
                if deletechars[j] == c {
                    is_del = true;
                }
                j += 1;
            }
            if !is_del {
                origs.push(c);
                row.push(table_lookup(table, c));
            }
            k += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}