use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(ops: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else if n <= ops.len() {
        sum(ops, (n - 1) as nat) + ops[(n - 1) as int]
    } else {
        sum(ops, ops.len())
    }
}

fn main() {
}

fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures
        result <==> exists n: nat :: n <= ops.len() && sum(ops, n) < 0
{
    let mut i: usize = 0;
    let mut current_sum: int = 0;
    
    while i < ops.len()
        invariant
            i <= ops.len(),
            current_sum == sum(ops, i as nat),
            forall j: nat :: j < i ==> sum(ops, j) >= 0,
    {
        current_sum = current_sum + ops[i as int];
        i = i + 1;
        
        if current_sum < 0 {
            assert(current_sum == sum(ops, i as nat));
            assert(sum(ops, i as nat) < 0);
            assert(i as nat <= ops.len());
            return true;
        }
    }
    
    assert(i == ops.len());
    assert(forall j: nat :: j < i ==> sum(ops, j) >= 0);
    assert(forall j: nat :: j <= ops.len() ==> sum(ops, j) >= 0) by {
        assert(forall j: nat :: j < ops.len() ==> sum(ops, j) >= 0);
        assert(sum(ops, ops.len()) == current_sum);
        assert(current_sum >= 0);
    }
    return false;
}

}