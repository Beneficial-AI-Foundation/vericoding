use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_from_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(s[i]),
{
    assert(s.contains(s[i]));
}
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    // post-conditions-start
    ensures
        ({
            let a = res.0;
            let b = res.1;
            &&& a.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] >= 0
            &&& a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0
            &&& a.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= a.unwrap()
            &&& b.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] <= 0
            &&& b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0
            &&& b.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= b.unwrap()
        }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut a: Option<i32> = None;
    let mut b: Option<i32> = None;
    let ghost mut a_idx: Option<int> = None;
    let ghost mut b_idx: Option<int> = None;

    let mut i: usize = 0;
    while i < n
        decreases arr@.len() - i as int
        invariant
            n == arr.len(),
            0 <= i as int <= arr@.len(),
            a.is_some() == a_idx.is_some(),
            b.is_some() == b_idx.is_some(),
            a.is_none() ==> forall|j: int| 0 <= j < i as int ==> #[trigger] arr@[j] >= 0i32,
            a.is_some() ==> a_idx.is_some(),
            a.is_some() ==> 0 <= a_idx.unwrap() < i as int,
            a.is_some() ==> a.unwrap() == arr@[a_idx.unwrap()],
            a.is_some() ==> a.unwrap() < 0i32,
            a.is_some() ==> forall|j: int|
                0 <= j < i as int && arr@[j] < 0i32 ==> #[trigger] arr@[j] <= a.unwrap(),
            b.is_none() ==> forall|j: int| 0 <= j < i as int ==> #[trigger] arr@[j] <= 0i32,
            b.is_some() ==> b_idx.is_some(),
            b.is_some() ==> 0 <= b_idx.unwrap() < i as int,
            b.is_some() ==> b.unwrap() == arr@[b_idx.unwrap()],
            b.is_some() ==> b.unwrap() > 0i32,
            b.is_some() ==> forall|j: int|
                0 <= j < i as int && arr@[j] > 0i32 ==> #[trigger] arr@[j] >= b.unwrap(),
    {
        let x = arr[i];
        assert(arr@[i as int] == x);
        if x < 0i32 {
            match a {
                None => {
                    a = Some(x);
                    proof { a_idx = Some(i as int); }
                }
                Some(y) => {
                    if x > y {
                        a = Some(x);
                        proof { a_idx = Some(i as int); }
                    }
                }
            }
        }
        if x > 0i32 {
            match b {
                None => {
                    b = Some(x);
                    proof { b_idx = Some(i as int); }
                }
                Some(y) => {
                    if x < y {
                        b = Some(x);
                        proof { b_idx = Some(i as int); }
                    }
                }
            }
        }
        i = i + 1;
    }

    proof {
        assert(i >= n);
        assert(i as int >= n as int);
        assert(i as int <= arr@.len());
        assert(arr@.len() == n as int);
        assert(i as int == arr@.len());

        if a.is_some() {
            assert(a_idx.is_some());
            let k = a_idx.unwrap();
            assert(0 <= k < arr@.len());
            assert(a.unwrap() == arr@[k]);
            lemma_seq_contains_from_index::<i32>(arr@, k);
            assert(arr@.contains(arr@[k]));
            assert(arr@.contains(a.unwrap()));
        }
        if b.is_some() {
            assert(b_idx.is_some());
            let k = b_idx.unwrap();
            assert(0 <= k < arr@.len());
            assert(b.unwrap() == arr@[k]);
            lemma_seq_contains_from_index::<i32>(arr@, k);
            assert(arr@.contains(arr@[k]));
            assert(arr@.contains(b.unwrap()));
        }
    }

    (a, b)
}
// </vc-code>

fn main() {}
}