// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn rfind_one(a: String, sub: String, start: int, end_pos: int) -> int
    requires
        0 <= start && start <= end_pos,
    ensures
        (result == -1 || (0 <= result && result < a@.len())),
        (result == -1 ==> forall|j: int| start <= j && j + sub@.len() <= end_pos + 1 && j + sub@.len() <= a@.len() ==> !string_starts_with(a@, sub@, j)),
        (result >= 0 ==> start <= result && result + sub@.len() <= end_pos + 1 && string_starts_with(a@, sub@, result) && (forall|j: int| result < j && j + sub@.len() <= end_pos + 1 && start <= j && j + sub@.len() <= a@.len() ==> !string_starts_with(a@, sub@, j))),
{
    let alen: int = a@.len() as int;
    let slen: int = sub@.len() as int;
    let mut best: int = -1;

    let endj: int = end_pos - slen + 1;
    let mut hi: int;
    let alen_minus: int = alen - slen;
    if endj < alen_minus {
        hi = endj;
    } else {
        hi = alen_minus;
    }

    if hi >= start {
        let mut curr: int = hi;
        while curr >= start
            invariant
                curr >= start - 1,
                (best == -1 || (start <= best && best + slen <= end_pos + 1 && string_starts_with(a@, sub@, best))),
                forall|k: int| best < k && k <= hi && k > curr && k + slen <= end_pos + 1 && start <= k && k + slen <= alen ==> !string_starts_with(a@, sub@, k),
            decreases curr - start + 1
        {
            if string_starts_with(a@, sub@, curr) {
                best = curr;
                // found the rightmost occurrence, exit
                curr = start - 1;
            } else {
                curr = curr - 1;
            }
        }
    }

    best
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
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    result.reserve(n);
    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i && i <= n as int,
            result.len() == i as usize,
            forall|t: int| 0 <= t && t < i ==> (
                (result[t as usize] == -1 || (0 <= result[t as usize] && (result[t as usize] as int) < a[t as usize]@.len())) ,
                (result[t as usize] == -1 ==> forall|j: int| (start[t as usize] as int) <= j && j + sub[t as usize]@.len() <= (end_pos[t as usize] as int) + 1 && j + sub[t as usize]@.len() <= a[t as usize]@.len() ==> !string_starts_with(a[t as usize]@, sub[t as usize]@, j)),
                (result[t as usize] >= 0 ==> (start[t as usize] as int) <= (result[t as usize] as int) && (result[t as usize] as int) + sub[t as usize]@.len() <= (end_pos[t as usize] as int) + 1 && string_starts_with(a[t as usize]@, sub[t as usize]@, result[t as usize] as int) && (forall|j: int| (result[t as usize] as int) < j && j + sub[t as usize]@.len() <= (end_pos[t as usize] as int) + 1 && (start[t as usize] as int) <= j && j + sub[t as usize]@.len() <= a[t as usize]@.len() ==> !string_starts_with(a[t as usize]@, sub[t as usize]@, j)))
            ),
        decreases n as int - i
    {
        let ai = a[i as usize].clone();
        let subi = sub[i as usize].clone();
        let s_idx = rfind_one(ai, subi, start[i as usize] as int, end_pos[i as usize] as int);
        result.push(s_idx as i32);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}