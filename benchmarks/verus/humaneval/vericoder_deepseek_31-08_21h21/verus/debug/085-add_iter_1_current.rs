use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}
// pure-end
// pure-end

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// pure-end

// <vc-helpers>
proof fn add_odd_evens_decreases(l: Seq<u32>, i: int) 
    requires 
        0 <= i <= l.len(),
    ensures 
        add_odd_evens(l.skip(i)) == if l.len() - i < 2 {
            0
        } else {
            odd_or_zero(l@[i + 1]) + add_odd_evens(l.skip(i + 2))
        }
    decreases l.len() - i,
{
    if i < l.len() {
        reveal(add_odd_evens);
        add_odd_evens_decreases(l, i + 2);
    }
}

lemma fn skip_len_geq_2<A>(s: Seq<A>, n: nat)
    requires n + 2 <= s.len(),
    ensures s.skip(n)@[1] == s@[n + 1]
{}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)
    // pre-conditions-start
    requires
        0 < lst.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == add_odd_evens(lst@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            i % 2 == 1,
            sum == add_odd_evens(lst@.skip(0).take(i)),
        decreases lst.len() - i,
    {
        proof {
            add_odd_evens_decreases(lst@, 0);
            skip_len_geq_2(lst@, i - 1);
        }
        
        let current = lst[i] as u64;
        if lst[i] % 2 == 0 {
            sum = sum + current;
        }
        
        i = i + 2;
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}