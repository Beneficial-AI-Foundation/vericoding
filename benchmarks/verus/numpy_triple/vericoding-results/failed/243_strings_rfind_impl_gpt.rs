// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): switch runtime indices to usize/i32, keep specs in invariants */
fn eq_at_exec(s: &String, p: &String, pos: i32) -> (res: bool)
    requires
        0 <= pos as int,
        (pos as int) + p@.len() <= s@.len(),
    ensures
        res ==> string_starts_with(s@, p@, pos as int),
        !res ==> !string_starts_with(s@, p@, pos as int),
{
    let mut k: usize = 0;
    let p_len: usize = p.len();
    while k < p_len
        invariant
            0 <= pos as int,
            (pos as int) + p@.len() <= s@.len(),
            0 <= k as int,
            k as int <= p@.len(),
            forall|i: int| 0 <= i && i < k as int ==> s[(pos as int) + i] == p[i],
        decreases p_len - k
    {
        let idx: usize = (pos as usize) + k;
        let sc = s.char_at(idx);
        let pc = p.char_at(k);
        if sc != pc { return false; }
        k = k + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>, start_pos: int) -> bool {
    start_pos >= 0 && start_pos + prefix.len() <= s.len() &&
    forall|i: int| 0 <= i < prefix.len() ==> s[start_pos + i] == prefix[i]
}

fn rfind(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < start.len() ==> 0 <= start[i] && start[i] <= end_pos[i],
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            /* Basic range constraint: result is -1 or within string bounds */
            (result[i] == -1 || (0 <= result[i] && result[i] < a[i]@.len())) &&
            /* If result is -1, no occurrence of substring within the specified range */
            (result[i] == -1 ==> 
                forall|j: int| start[i] <= j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                               j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)) &&
            /* If result is non-negative, it's the rightmost valid occurrence */
            (result[i] >= 0 ==> 
                /* The result is within the search range */
                start[i] <= result[i] && 
                result[i] + sub[i]@.len() <= end_pos[i] + 1 &&
                /* The substring matches at this position */
                string_starts_with(a[i]@, sub[i]@, result[i] as int) &&
                /* This is the rightmost occurrence within the range */
                (forall|j: int| result[i] < j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                                start[i] <= j && j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)))
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid ghost int/nat in exec; use i32/usize with proofs for specs */
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            sub.len() == n,
            start.len() == n,
            end_pos.len() == n,
            result.len() as int == i as int,
            forall|k: int| 0 <= k && k < i as int ==> (
                (result[k as usize] == -1 || (0 <= result[k as usize] && (result[k as usize] as int) < a[k as usize]@.len())) &&
                (result[k as usize] == -1 ==>
                    forall|j: int| start[k as usize] as int <= j && j + sub[k as usize]@.len() <= end_pos[k as usize] as int + 1 &&
                                   j + sub[k as usize]@.len() <= a[k as usize]@.len() ==>
                        !string_starts_with(a[k as usize]@, sub[k as usize]@, j)) &&
                (result[k as usize] >= 0 ==> (
                    start[k as usize] as int <= result[k as usize] as int &&
                    (result[k as usize] as int) + sub[k as usize]@.len() <= end_pos[k as usize] as int + 1 &&
                    (result[k as usize] as int) + sub[k as usize]@.len() <= a[k as usize]@.len() &&
                    string_starts_with(a[k as usize]@, sub[k as usize]@, result[k as usize] as int) &&
                    (forall|j: int| (result[k as usize] as int) < j && j + sub[k as usize]@.len() <= end_pos[k as usize] as int + 1 &&
                                       start[k as usize] as int <= j && j + sub[k as usize]@.len() <= a[k as usize]@.len() ==>
                        !string_starts_with(a[k as usize]@, sub[k as usize]@, j))
                ))
            ),
        decreases n - i
    {
        let s = &a[i];
        let p = &sub[i];
        let st = start[i];
        let en = end_pos[i];

        let s_len_usize: usize = s.len();
        let p_len_usize: usize = p.len();
        let s_len_i32: i32 = s_len_usize as i32;
        let p_len_i32: i32 = p_len_usize as i32;

        let mut res_i: i32 = -1;

        if p_len_usize == 0 {
            let mut r: i32 = en + 1;
            if r > s_len_i32 { r = s_len_i32; }
            if r < st { r = st; }
            res_i = r;
            proof {
                assert(string_starts_with(s@, p@, res_i as int));
                assert(start[i] as int <= res_i as int);
                assert((res_i as int) + p@.len() <= end_pos[i] as int + 1);
                assert((res_i as int) + p@.len() <= s@.len());
                assert(forall|j: int| (res_i as int) < j && j + p@.len() <= end_pos[i] as int + 1 && start[i] as int <= j && j + p@.len() <= s@.len() ==> !string_starts_with(s@, p@, j));
            }
        } else {
            let mut hi: i32 = en + 1 - p_len_i32;
            let cap: i32 = s_len_i32 - p_len_i32;
            if hi > cap { hi = cap; }

            let mut j: i32 = hi;
            while j >= st
                invariant
                    (j as int) < st as int || ((j as int) + p@.len() <= en as int + 1 && (j as int) + p@.len() <= s@.len()),
                    forall|k: int| (j as int) < k && k + p@.len() <= en as int + 1 && st as int <= k && k + p@.len() <= s@.len() ==> !string_starts_with(s@, p@, k),
                decreases if j >= st { (j - st) as nat } else { 0 }
            {
                if j >= 0 && j + p_len_i32 <= s_len_i32 {
                    proof {
                        let s_len_int: int = s_len_usize as int;
                        let p_len_int: int = p_len_usize as int;
                        assert(s_len_int == s@.len());
                        assert(p_len_int == p@.len());
                        assert(0 <= j as int);
                        assert((j as int) + p_len_int <= s_len_int);
                    }
                    if eq_at_exec(s, p, j) {
                        res_i = j;
                        break;
                    } else {
                        proof { assert(!string_starts_with(s@, p@, j as int)); }
                    }
                }
                if j == st { break; }
                j = j - 1;
            }
            if res_i != -1 {
                proof {
                    let rr = res_i as int;
                    assert(st as int <= rr);
                    assert(rr + p@.len() <= en as int + 1);
                    assert(rr + p@.len() <= s@.len());
                    assert(string_starts_with(s@, p@, rr));
                    assert(forall|k: int| rr < k && k + p@.len() <= en as int + 1 && st as int <= k && k + p@.len() <= s@.len() ==> !string_starts_with(s@, p@, k));
                }
            } else {
                proof {
                    assert(forall|k: int| st as int <= k && k + p@.len() <= en as int + 1 && k + p@.len() <= s@.len() ==> !string_starts_with(s@, p@, k));
                }
            }
        }

        result.push(res_i);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}