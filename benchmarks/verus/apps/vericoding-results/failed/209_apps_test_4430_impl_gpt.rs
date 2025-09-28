// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn greedy_pack_from_end(a: Seq<int>, boxes: int, capacity: int) -> int
    recommends
        boxes >= 1,
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
{
    greedy_pack_from_end_helper(a, a.len() - 1, boxes, capacity, capacity)
}

spec fn greedy_pack_from_end_helper(a: Seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int) -> int
    recommends
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
        boxes_left >= 1,
        0 <= current_box_space <= capacity,
    decreases pos + 1,
{
    if pos < 0 {
        0int
    } else if pos >= a.len() {
        0int
    } else if a[pos] > capacity {
        0int
    } else if a[pos] <= current_box_space {
        1int + greedy_pack_from_end_helper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos])
    } else if boxes_left > 1 {
        1int + greedy_pack_from_end_helper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos])
    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma linking Seq map index for i8->int conversion */
proof fn lemma_map_index_i8_to_int(a: Seq<i8>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        a.map(|j, x| x as int)[i] == a[i] as int,
{
    assert(a.map(|j, x| x as int)[i] == a[i] as int);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8, a: Vec<i8>) -> (result: i8)
    requires
        n >= 0,
        m >= 1,
        k >= 1,
        a.len() == n as usize,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] as int >= 1 && #[trigger] a[i] as int <= k as int,
    ensures
        0 <= result as int <= n as int,
        result as int == greedy_pack_from_end(a@.map(|i, x| x as int), m as int, k as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid a@.len() in invariants; maintain greedy correctness invariant */
    let mi: i32 = m as i32;
    let ki: i32 = k as i32;
    let total_len: i32 = a.len() as i32;
    let mut pos: i32 = total_len - 1;
    let mut boxes_left: i32 = mi;
    let mut space: i32 = ki;
    let mut res: i32 = 0;

    while pos >= 0 && (pos as usize) < a.len() && ((a[pos as usize] as i32) <= space || boxes_left > 1)
        invariant
            -1 <= pos as int,
            pos as int < a.len() as int,
            1 <= boxes_left as int,
            boxes_left as int <= m as int,
            0 <= space as int,
            space as int <= k as int,
            0 <= res as int,
            res as int + pos as int + 1 == a.len() as int,
            res as int + greedy_pack_from_end_helper(a@.map(|i, x| x as int), pos as int, boxes_left as int, k as int, space as int) == greedy_pack_from_end(a@.map(|i, x| x as int), m as int, k as int),
        decreases pos as int + 1
    {
        let w_i32: i32 = a[pos as usize] as i32;
        proof {
            assert(a@.len() == a.len() as int);
            assert(0 <= pos as int && pos as int < a@.len());
            assert(a@[pos as int] == a[pos as usize]);
            lemma_map_index_i8_to_int(a@, pos as int);
            let s = a@.map(|i, x| x as int);
            assert(s[pos as int] == (a@[pos as int]) as int);
            assert(1 <= a[pos as usize] as int && a[pos as usize] as int <= k as int);
        }
        if w_i32 <= space {
            proof {
                let s = a@.map(|i, x| x as int);
                assert(s[pos as int] == a[pos as usize] as int);
                assert((a[pos as usize] as i32) <= space);
                assert(s[pos as int] <= space as int);
                assert(
                    greedy_pack_from_end_helper(s, pos as int, boxes_left as int, k as int, space as int)
                    ==
                    1int + greedy_pack_from_end_helper(s, (pos as int) - 1, boxes_left as int, k as int, (space as int) - s[pos as int])
                );
            }
            res = res + 1;
            space = space - w_i32;
            pos = pos - 1;
        } else {
            proof {
                let s = a@.map(|i, x| x as int);
                assert(s[pos as int] == a[pos as usize] as int);
                assert((a[pos as usize] as i32) > space);
                assert(!(w_i32 <= space));
                assert(boxes_left > 1);
                assert(s[pos as int] > space as int);
                assert(
                    greedy_pack_from_end_helper(s, pos as int, boxes_left as int, k as int, space as int)
                    ==
                    1int + greedy_pack_from_end_helper(s, (pos as int) - 1, (boxes_left as int) - 1, k as int, (k as int) - s[pos as int])
                );
            }
            res = res + 1;
            boxes_left = boxes_left - 1;
            space = ki - w_i32;
            pos = pos - 1;
        }
    }
    proof {
        let s = a@.map(|i, x| x as int);
        if pos < 0 {
            assert(greedy_pack_from_end_helper(s, pos as int, boxes_left as int, k as int, space as int) == 0int);
        } else {
            assert(a@.len() == a.len() as int);
            assert(0 <= pos as int && pos as int < a@.len());
            assert(!((a[pos as usize] as i32) <= space || boxes_left > 1));
            assert((a[pos as usize] as i32) > space);
            assert(!(boxes_left > 1));
            assert(1 <= boxes_left as int && boxes_left as int <= 1);
            assert(boxes_left == 1);
            lemma_map_index_i8_to_int(a@, pos as int);
            assert(s[pos as int] == a[pos as usize] as int);
            assert(s[pos as int] > space as int);
            assert((a[pos as usize] as int) >= 1 && (a[pos as usize] as int) <= k as int);
            assert(greedy_pack_from_end_helper(s, pos as int, boxes_left as int, k as int, space as int) == 0int);
        }
        assert(res as int + greedy_pack_from_end_helper(s, pos as int, boxes_left as int, k as int, space as int) == greedy_pack_from_end(s, m as int, k as int));
        assert(res as int == greedy_pack_from_end(s, m as int, k as int));

        assert(-1 <= pos as int);
        assert(res as int + pos as int + 1 == a.len() as int);
        assert(0 <= pos as int + 1);
        assert(res as int <= a.len() as int);
    }
    res as i8
}
// </vc-code>


}

fn main() {}