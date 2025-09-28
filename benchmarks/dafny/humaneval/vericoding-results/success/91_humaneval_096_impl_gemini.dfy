// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): reviewed and confirmed correctness */
method IsPrime(num: int) returns (is_p: bool)
    requires num >= 2
    ensures is_p <==> is_prime_number(num)
{
    var k := 2;
    while k < num
        invariant 2 <= k <= num
        invariant forall j :: 2 <= j < k ==> num % j != 0
        decreases num - k
    {
        if num % k == 0 {
            is_p := false;
            return;
        }
        k := k + 1;
    }
    is_p := true;
}
// </vc-helpers>

// <vc-spec>
method count_up_to(n: int) returns (result: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |result| ==> is_prime_number(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] < n
    ensures forall p :: 2 <= p < n && is_prime_number(p) ==> p in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): simplified loop invariants by handling n <= 2 as a special case */
    if n <= 2 {
        result := [];
        return;
    }
    result := [];
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 0 <= k < |result| ==> is_prime_number(result[k])
        invariant forall k :: 0 <= k < |result| ==> result[k] < i
        invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in result
        invariant forall k1, k2 :: 0 <= k1 < k2 < |result| ==> result[k1] < result[k2]
        decreases n - i
    {
        var is_i_prime := IsPrime(i);
        if is_i_prime {
            result := result + [i];
        }
        i := i + 1;
    }
}
// </vc-code>
