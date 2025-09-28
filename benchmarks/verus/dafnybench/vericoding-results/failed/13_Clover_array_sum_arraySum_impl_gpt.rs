use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut c: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == b.len(),
            i <= a.len(),
            i == c.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] c@[j] == a@[j] + b@[j],
    {
        let i_old = i;
        let ai = a[i_old];
        let bi = b[i_old];
        c.push(ai + bi);
        proof {
            assert(a@[i_old as int] == ai);
            assert(b@[i_old as int] == bi);
            assert(c@[i_old as int] == ai + bi);
            assert(c@[i_old as int] == a@[i_old as int] + b@[i_old as int]);
        }
        i += 1;
        proof {
            assert_forall_by(|j: int|
                requires 0 <= j < i as int,
                ensures c@[j] == a@[j] + b@[j],
            {
                if j < i_old as int {
                    assert(c@[j] == a@[j] + b@[j]);
                } else {
                    assert(j == i_old as int);
                    assert(c@[i_old as int] == a@[i_old as int] + b@[i_old as int]);
                }
            });
        }
    }
    c
}
// </vc-code>

fn main() {}

}