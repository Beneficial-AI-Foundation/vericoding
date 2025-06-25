// ATOM 
spec fn sum(s: Seq<int>, n: nat) -> int
    recommends n <= s.len()
{
    if s.len() == 0 || n == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int), (n-1) as nat)
    }
}

// ATOM 
proof fn sum_plus(s: Seq<int>, i: nat)
    requires i < s.len()
    ensures sum(s, i) + s[i as int] == sum(s, (i+1) as nat)
{
}

// SPEC 
pub fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
{
}