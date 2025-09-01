use vstd::prelude::*;

verus! {

// <vc-helpers>
fn filter_seq_positive(s: Seq<i32>) -> Seq<i32>
    ensures
        filter_seq_positive(s) == s.filter(|x: int| x > 0),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let head = s.index(0);
        let tail = s.drop_first(1);
        let filtered_tail = filter_seq_positive(tail);
        if head > 0 {
            Seq::new(1, |i: nat| {
                if i == 0 {
                    head
                } else {
                    unreachable!()
                }
            }).add(filtered_tail)
        } else {
            filtered_tail
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut positive_list: Vec<i32> = Vec::new();
    let mut i: nat = 0;

    #[verifier(loop_invariant)]
    #[allow(unused_assignments)]
    while (i < input.len() as nat)
        invariant
            0 <= i && i <= input.len() as nat,
            positive_list@ == filter_seq_positive(input@.subsequence(0, i)),
    {
        let x = input[i as usize];
        if x > 0 {
            positive_list.push(x);
        }
        i = i + 1;
    }

    assert(positive_list@ == filter_seq_positive(input@.subsequence(0, input.len() as nat)));
    assert(positive_list@ == input@.filter(|x: int| x > 0));

    positive_list
    // impl-end
}
// </vc-code>

fn main() {}
}