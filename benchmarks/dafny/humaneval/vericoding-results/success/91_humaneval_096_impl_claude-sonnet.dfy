// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>
function is_prime_below(p: int, n: int): bool
    requires p >= 0 && n >= 0
{
    p >= 2 && p < n && is_prime_number(p)
}

lemma prime_ordering_lemma(a: int, b: int)
    requires a >= 2 && b >= 2 && a < b
    ensures a != b
{
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
    /* code modified by LLM (iteration 3): handle n < 2 case to fix loop invariant */
    result := [];
    if n < 2 {
        return;
    }
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 0 <= k < |result| ==> is_prime_number(result[k])
        invariant forall k :: 0 <= k < |result| ==> result[k] < i
        invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in result
        invariant forall x, y :: 0 <= x < y < |result| ==> result[x] < result[y]
    {
        if is_prime_number(i) {
            result := result + [i];
        }
        i := i + 1;
    }
}
// </vc-code>
