use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn lemma_sum_fold_left(s: Seq<u32>)
    ensures spec_sum(s) == s.fold_left(0int, |x: int, y: u32| x + (y as int))
{
}

proof fn lemma_sum_empty()
    ensures spec_sum(Seq::<u32>::empty()) == 0
{
}

proof fn lemma_sum_single(x: u32)
    ensures spec_sum(seq![x]) == x as int
{
}

proof fn lemma_sum_cons(x: u32, s: Seq<u32>)
    ensures spec_sum(seq![x].add(s)) == (x as int) + spec_sum(s)
{
}

fn sum_iter(qs: &Vec<u32>) -> (ret: u32)
    requires spec_sum(qs@) <= u32::MAX
    ensures ret as int == spec_sum(qs@)
{
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    
    while i < qs.len()
        invariant
            i <= qs.len(),
            sum as int == spec_sum(qs@.subrange(0, i as int)),
            spec_sum(qs@) <= u32::MAX,
    {
        assert(qs@.subrange(0, i as int).add(seq![qs@[i as int]]) =~= qs@.subrange(0, (i + 1) as int));
        lemma_sum_cons(qs[i], qs@.subrange(0, i as int));
        sum = sum + qs[i];
        i = i + 1;
    }
    
    assert(qs@.subrange(0, i as int) =~= qs@);
    sum
}

fn is_palindrome(qs: &Vec<u32>) -> (ret: bool)
    ensures ret <==> qs@ =~= qs@.reverse()
{
    let len = qs.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            i <= len / 2,
            forall|j: int| 0 <= j < i ==> qs@[j] == qs@[len - 1 - j],
    {
        if qs[i] != qs[len - 1 - i] {
            assert(qs@[i as int] != qs@[(len - 1 - i) as int]);
            assert(qs@[i as int] != qs@.reverse()[i as int]);
            return false;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < len ==> qs@[j] == qs@[len - 1 - j]) by {
        assert(forall|j: int| 0 <= j < len / 2 ==> qs@[j] == qs@[len - 1 - j]);
        assert(forall|j: int| len / 2 <= j < len ==> {
            let k = len - 1 - j;
            &&& 0 <= k < len / 2
            &&& qs@[k] == qs@[len - 1 - k]
            &&& qs@[j] == qs@[k]
        });
    };
    
    assert(qs@ =~= qs@.reverse());
    true
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if spec_sum(qs@) > w {
        return false;
    }
    
    let palindrome_check = is_palindrome(qs);
    if !palindrome_check {
        return false;
    }
    
    let sum = sum_iter(qs);
    let weight_check = sum <= w;
    
    palindrome_check && weight_check
}
// </vc-code>

fn main() {}
}