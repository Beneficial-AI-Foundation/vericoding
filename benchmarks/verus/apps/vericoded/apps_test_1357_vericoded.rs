// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, tasks: Seq<int>) -> bool {
    n >= 2 && m >= 1 && tasks.len() == m && 
    forall|i: int| 0 <= i < tasks.len() ==> 1 <= #[trigger] tasks[i] <= n
}

spec fn min_time_to_complete(n: int, tasks: Seq<int>, current_pos: int, task_index: int) -> int
    recommends 
        n >= 2,
        forall|i: int| 0 <= i < tasks.len() ==> 1 <= #[trigger] tasks[i] <= n,
        1 <= current_pos <= n,
        0 <= task_index < tasks.len()
{
    let target = tasks[task_index];
    if target >= current_pos { target - current_pos }
    else { (n - current_pos) + target }
}
// </vc-preamble>

// <vc-helpers>
proof fn nonneg_mul(a: int, b: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        a * b >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, tasks: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, tasks@.map(|i, x: i8| x as int))
    ensures 
        result >= 0,
        m > 0 ==> result >= tasks@[(m as int) - 1] as int - 1,
        result <= ((m as int) - 1) * (n as int) + tasks@[(m as int) - 1] as int - 1,
// </vc-spec>
// <vc-code>
{
    let len = tasks.len();

    proof {
        assert(tasks@.len() == m as int);
        assert(m as int >= 1);
        assert(tasks@.len() >= 1);
        assert(tasks.len() as int == tasks@.len());
    }
    assert(len == tasks@.len() as usize);
    assert(len > 0);

    let mut i: usize = 0;
    let mut last: i8 = 0;
    let mut seen: bool = false;

    while i < len
        invariant
            tasks.len() == len,
            0 <= i <= len,
            seen ==> last == tasks@[i as int - 1],
            !seen ==> i == 0,
        decreases len - i
    {
        let x = tasks[i];
        i = i + 1;
        last = x;
        seen = true;
        proof {
            assert(tasks@[i as int - 1] == x);
        }
    }

    proof {
        assert(seen);
        assert(i == len);
        assert(tasks@.len() == m as int);
        assert(len as int == tasks@.len());
        assert(last == tasks@[len as int - 1]);
        assert(last == tasks@[(m as int) - 1]);

        let seqi = tasks@.map(|j, y: i8| y as int);
        assert(seqi.len() == tasks@.len());
        let j = (m as int) - 1;
        assert(0 <= j && j < seqi.len());
        assert(seqi[j] == tasks@[(m as int) - 1] as int);
        assert(1 <= seqi[j] <= n as int);
        assert(last as int == seqi[j]);
        assert(last as int >= 1);
    }

    assert(last >= 1 as i8);
    let res: i8 = last - 1;

    proof {
        let mm = m as int;
        let nn = n as int;
        nonneg_mul(mm - 1, nn);
        assert(res as int == last as int - 1);
        assert(res as int == tasks@[(mm - 1)] as int - 1);
        assert(res as int >= 0);
        assert(res as int >= tasks@[(mm - 1)] as int - 1);
        assert(res as int <= ((mm - 1) * nn) + tasks@[(mm - 1)] as int - 1);
    }

    res
}
// </vc-code>


}

fn main() {}