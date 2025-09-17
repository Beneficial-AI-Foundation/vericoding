// <vc-preamble>
// ======= TASK =======
// Given a non-negative integer n, return an array containing all prime numbers 
// that are strictly less than n, in ascending order.

// ======= SPEC REQUIREMENTS =======
predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}

// ======= HELPERS =======
method is_prime(num: int) returns (prime: bool)
    requires num >= 0
    ensures prime == is_prime_number(num)
{
    if num < 2 {
        prime := false;
    } else if num == 2 {
        prime := true;
    } else if num % 2 == 0 {
        prime := false;
    } else {
        prime := true;
        var i := 3;
        while i * i <= num
            invariant 3 <= i
            invariant i % 2 == 1
            invariant prime == (forall k :: 3 <= k < i && k % 2 == 1 ==> num % k != 0)
            invariant prime ==> (forall k :: 2 <= k < i ==> num % k != 0)
            invariant !prime ==> (exists k :: 2 <= k < num && num % k == 0)
        {
            if num % i == 0 {
                prime := false;
                break;
            }
            i := i + 2;
        }

        if prime {
            assert forall k :: 2 <= k < i ==> num % k != 0;
            assert i * i > num;
            assert forall k :: i <= k < num ==> k >= i;
            assert forall k :: i <= k < num ==> k * k >= i * i > num;
            assert forall k :: i <= k < num ==> k > num / k;
            assert forall k :: i <= k < num ==> (num % k == 0 ==> num % (num / k) == 0 && 2 <= num / k < i);
            assert forall k :: 2 <= k < num ==> num % k != 0;
        }
    }
}
// </vc-preamble>

// <vc-helpers>
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
    result := [];
    if n <= 2 {
        return;
    }
    var i := 2;
    while i < n
        invariant 2 <= i
        invariant i <= n
        invariant forall k :: 0 <= k < |result| ==> is_prime_number(result[k])
        invariant forall k :: 0 <= k < |result| ==> result[k] < n
        invariant forall k :: 0 <= k < |result| ==> result[k] < i
        invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in result
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] < result[j]
    {
        var is_prime_result := is_prime(i);
        if is_prime_result {
            result := result + [i];
        }
        i := i + 1;
    }
}
// </vc-code>
