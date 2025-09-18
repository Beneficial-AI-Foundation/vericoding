// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec for membership of delete set */
spec fn not_deleted(c: u8, deletes: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < deletes.len() ==> c != deletes[j]
}

/* helper modified by LLM (iteration 5): spec describing correctness of a translated row */
spec fn row_ok(a_row: Seq<u8>, out_row: Seq<u8>, table: Seq<u8>, deletes: Seq<u8>) -> bool {
    out_row.len() <= a_row.len() &&
    (forall|c: u8| #[trigger] out_row.contains(c) ==> not_deleted(c, deletes)) &&
    (forall|k: int| 0 <= k < out_row.len() ==> {
        exists|orig_char: u8, table_idx: int|
            0 <= table_idx < 256 &&
            orig_char == table_idx as u8 &&
            #[trigger] out_row[k] == table[table_idx] &&
            a_row.contains(orig_char) &&
            not_deleted(orig_char, deletes)
    }) &&
    (forall|orig_char: u8| #[trigger] a_row.contains(orig_char) ==> {
        not_deleted(orig_char, deletes) ==> {
            exists|translated_char: u8| out_row.contains(translated_char) &&
                exists|table_idx: int|
                    0 <= table_idx < 256 &&
                    orig_char as int == table_idx &&
                    translated_char == table[table_idx]
        }
    }) &&
    (deletes.len() == 0 ==> {
        out_row.len() == a_row.len() &&
        (forall|k: int| 0 <= k < a_row.len() ==> {
            exists|table_idx: int|
                0 <= table_idx < 256 &&
                a_row[k] as int == table_idx &&
                #[trigger] out_row[k] == table[table_idx]
        })
    }) &&
    (a_row.len() == 0 ==> out_row.len() == 0)
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
    /* code modified by LLM (iteration 5): implement translation with loop invariants and spec helpers; fix chained inequalities */
    let n = a.len();
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant result.len() == i
        invariant a.len() == n
        invariant table.len() == 256
        invariant forall|m: int| 0 <= m < i ==> row_ok(a[m]@, result[m]@, table@, deletechars@)
    {
        let row = &a[i as nat];
        let rowlen = row.len();
        let mut out: Vec<u8> = Vec::new();
        let mut j: int = 0;
        if deletechars.len() == 0 {
            while j < rowlen
                invariant 0 <= j && j <= rowlen
                invariant out.len() == j
                invariant forall|k: int| 0 <= k < j ==> out@[k] == table@[row@[k] as int]
            {
                let c = row[j as nat];
                j += 1;
                assert((c as int) < table.len());
                let t = table[c as nat];
                out.push(t);
            }
            proof {
                assert(out.len() == row.len());
                assert(forall|k: int| 0 <= k < row.len() ==> out@[k] == table@[row@[k] as int]);
            }
        } else {
            while j < rowlen
                invariant 0 <= j && j <= rowlen
                invariant out.len() <= j
                invariant forall|c: u8| #[trigger] out@.contains(c) ==> not_deleted(c, deletechars@)
                invariant forall|k: int| 0 <= k < out.len() ==> exists|p: int| 0 <= p < j && not_deleted(row@[p], deletechars@) && out@[k] == table@[row@[p] as int]
                invariant forall|p: int| 0 <= p < j && not_deleted(row@[p], deletechars@) ==> #[trigger] out@.contains(table@[row@[p] as int])
            {
                let c = row[j as nat];
                j += 1;
                let mut del_found: bool = false;
                let mut d: int = 0;
                while d < deletechars.len()
                    invariant 0 <= d && d <= deletechars.len()
                    invariant del_found ==> exists|t: int| 0 <= t < d && deletechars@[t] == c
                    invariant !del_found ==> forall|t: int| 0 <= t < d ==> deletechars@[t] != c
                {
                    let dc = deletechars[d as nat];
                    if dc == c {
                        del_found = true;
                    }
                    d += 1;
                }
                if !del_found {
                    assert(d == deletechars.len());
                    assert(forall|t: int| 0 <= t < deletechars.len() ==> deletechars@[t] != c);
                    assert(not_deleted(c, deletechars@));
                    assert((c as int) < table.len());
                    let tval = table[c as nat];
                    out.push(tval);
                }
            }
        }
        proof {
            if deletechars.len() == 0 {
                assert(row_ok(row@, out@, table@, deletechars@));
            } else {
                assert(j == rowlen);
                assert(row_ok(row@, out@, table@, deletechars@));
            }
        }
        result.push(out);
        assert(row_ok(a[i as nat]@, result[i as nat]@, table@, deletechars@));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}