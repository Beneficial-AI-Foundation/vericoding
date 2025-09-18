// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    spec fn contains(seq: Seq<u8>, c: u8) -> bool {
        exists|i: int| 0 <= i < seq.len() && seq[i] == c
    }

    spec fn all_chars_kept(single_char: u8, deletechars: Vec<u8>) -> bool {
        forall|j: int| 0 <= j < deletechars.len() ==> single_char != deletechars[j]
    }

    /* helper modified by LLM (iteration 5): Added decreases clause to recursive lemma */
    proof fn translation_correct(index: int, a_seq: Seq<u8>, result_seq: Seq<u8>, table: Vec<u8>, deletechars: Vec<u8>)
        decreases index
        requires
            index == a_seq.len(),
            table.len() == 256,
            result_seq == translation_loop(a_seq, table, deletechars, 0, seq![]),
        ensures
            result_seq.len() == translation_result_len(a_seq, deletechars, 0),
            forall|c: u8| #[trigger] result_seq.contains(c) ==> {
                forall|j: int| 0 <= j < deletechars.len() ==> c != deletechars[j]
            },
            forall|k: int| 0 <= k < result_seq.len() ==> {
                exists|orig_char: u8, table_idx: int|
                    0 <= table_idx < 256 &&
                    orig_char == table_idx as u8 &&
                    result_seq[k] == table[table_idx] &&
                    a_seq.contains(orig_char) &&
                    (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j])
            },
            forall|orig_char: u8| #[trigger] a_seq.contains(orig_char) ==> {
                (forall|j: int| 0 <= j < deletechars.len() ==> orig_char != deletechars[j]) ==> {
                    exists|translated_char: u8| result_seq.contains(translated_char) &&
                        exists|table_idx: int|
                            0 <= table_idx < 256 &&
                            orig_char as int == table_idx &&
                            translated_char == table[table_idx]
                }
            },
            (deletechars.len() == 0 ==> {
                result_seq.len() == a_seq.len() &&
                forall|k: int| 0 <= k < a_seq.len() ==> {
                    exists|table_idx: int|
                        0 <= table_idx < 256 &&
                        a_seq[k] as int == table_idx &&
                        result_seq[k] == table[table_idx]
                }
            }) &&
            (a_seq.len() == 0 ==> result_seq.len() == 0)
    {
        if index == 0 {
            assert(result_seq =~= seq![]);
        } else {
            let prev_seq = a_seq.subrange(0, index - 1);
            translation_correct(index - 1, prev_seq, translation_loop(prev_seq, table, deletechars, 0, seq![]), table, deletechars);
            let last_char = a_seq[index - 1];
            if all_chars_kept(last_char, deletechars) {
                let table_idx = last_char as int;
                assert(0 <= table_idx < 256);
                let translated_char = table[table_idx];
                assert(result_seq =~= translation_loop(prev_seq, table, deletechars, 0, seq![]).push(translated_char));
            } else {
                assert(result_seq =~= translation_loop(prev_seq, table, deletechars, 0, seq![]));
            }
        }
    }

    spec fn translation_loop(s: Seq<u8>, table: Vec<u8>, deletechars: Vec<u8>, pos: int, acc: Seq<u8>) -> Seq<u8>
        recommends
            pos >= 0,
        decreases s.len() - pos,
    {
        if pos >= s.len() {
            acc
        } else {
            let current_char = s[pos];
            if all_chars_kept(current_char, deletechars) {
                let table_idx = current_char as int;
                translation_loop(s, table, deletechars, pos + 1, acc.push(table[table_idx]))
            } else {
                translation_loop(s, table, deletechars, pos + 1, acc)
            }
        }
    }

    spec fn translation_result_len(s: Seq<u8>, deletechars: Vec<u8>, pos: int) -> int
        recommends
            pos >= 0,
        decreases s.len() - pos,
    {
        if pos >= s.len() {
            0
        } else {
            let current_char = s[pos];
            let increment: int = if all_chars_kept(current_char, deletechars) { 1 } else { 0 };
            increment + translation_result_len(s, deletechars, pos + 1)
        }
    }

    proof fn translation_loop_len_correct(s: Seq<u8>, table: Vec<u8>, deletechars: Vec<u8>, pos: int, acc: Seq<u8>)
        requires
            table.len() == 256,
            pos >= 0,
            acc.len() == translation_result_len(s.subrange(0, pos), deletechars, 0),
        ensures
            translation_loop(s, table, deletechars, pos, acc).len() == translation_result_len(s, deletechars, 0)
        decreases s.len() - pos,
    {
        if pos < s.len() {
            let current_char = s[pos];
            let kept = all_chars_kept(current_char, deletechars);
            let new_pos = pos + 1;
            let new_acc = if kept {
                let table_idx = current_char as int;
                acc.push(table[table_idx])
            } else {
                acc
            };
            assert(new_acc.len() == acc.len() + (if kept { 1int } else { 0int }));
            assert(new_acc.len() == translation_result_len(s.subrange(0, new_pos), deletechars, 0));
            translation_loop_len_correct(s, table, deletechars, new_pos, new_acc);
        }
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
    /* code modified by LLM (iteration 5): Fixed compilation error by adding proper loop invariants */
    let mut result: Vec<Vec<u8>> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let input_row = a[j].view();
                let output_row = result[j].view();
                output_row.len() <= input_row.len()
            }
    {
        let input_row = &a[i];
        let mut output_row: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < input_row.len()
            invariant
                j <= input_row.len(),
                output_row.len() <= j
        {
            let current_char = input_row[j];
            let mut should_keep = true;
            let mut k: usize = 0;
            while k < deletechars.len()
                invariant
                    k <= deletechars.len(),
                    should_keep == forall|l: int| 0 <= l < k ==> current_char != deletechars[l]
            {
                if current_char == deletechars[k] {
                    should_keep = false;
                    break;
                }
                k += 1;
            }
            if should_keep {
                let table_idx = current_char as usize;
                assert(0 <= table_idx && table_idx < 256);
                let translated_char = table[table_idx];
                output_row.push(translated_char);
            }
            j += 1;
        }
        result.push(output_row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}