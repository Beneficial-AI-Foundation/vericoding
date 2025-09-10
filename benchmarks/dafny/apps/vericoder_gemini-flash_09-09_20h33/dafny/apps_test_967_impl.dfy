predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= n) &&
    (forall i, j :: 0 <= i < j < n ==> a[i] != a[j])
}

predicate ValidOutput(n: int, result: int)
{
    0 <= result <= n
}

function ReversedArray(a: seq<int>): seq<int>
    requires |a| >= 1
    ensures |ReversedArray(a)| == |a|
{
    seq(|a|, i requires 0 <= i < |a| => a[|a|-1-i])
}

predicate HasIncreasingPair(ar: seq<int>)
{
    exists i :: 1 <= i < |ar| && ar[i] > ar[i-1]
}

function CorrectResult(n: int, a: seq<int>): int
    requires ValidInput(n, a)
    ensures ValidOutput(n, CorrectResult(n, a))
{
    var ar := ReversedArray(a);
    if HasIncreasingPair(ar) then
        var min_i := MinIndex(ar, n);
        n - min_i
    else
        0
}

// <vc-helpers>
function MinIndex(a: seq<int>, n: int): int
    requires n >= 1
    requires |a| == n
    // The following precondition ensures that if a reversed array `ar` has an increasing pair,
    // then MinIndex will find that index. This strengthens the helper for its use in `solve`.
    requires var ar_temp := ReversedArray(a); HasIncreasingPair(ar_temp)
    ensures 0 <= MinIndex(a, n) < n
    ensures var ar_temp := ReversedArray(a); forall k_less :: 1 <= k_less < MinIndex(a, n) ==> ar_temp[k_less] <= ar_temp[k_less-1]
    ensures var ar_temp := ReversedArray(a); MinIndex(a,n) > 0 ==> ar_temp[MinIndex(a,n)] > ar_temp[MinIndex(a,n)-1]
{
    var ar := ReversedArray(a);
    var k := 1;
    while k < n
        invariant 1 <= k <= n
        invariant forall i :: 1 <= i < k ==> ar[i] <= ar[i-1]
        // This loop invariant is critical: if HasIncreasingPair is true,
        // then an increasing pair must exist at or after 'k'.
        invariant HasIncreasingPair(ar[k..]) || (forall i :: 1 <= i < k ==> ar[i] <= ar[i-1]) && !HasIncreasingPair(ar[k+1..])
        // Updated invariant to be more precise for loop termination and correctness
        invariant HasIncreasingPair(ar) ==> (exists j :: k <= j < n && ar[j] > ar[j-1])
    {
        if ar[k] > ar[k-1] then
            return k;
        k := k + 1;
    }
    // This return statement should only be reachable if the HasIncreasingPair
    // precondition was violated, or if the increasing pair is at the very last
    // possible index. Given the specification, an increasing pair must be found.
    // We return 'n-1' as a fallback, although logical reasoning with
    // preconditions should guarantee a 'return k' within the loop.
    n-1
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(n, result)
    ensures result == CorrectResult(n, a)
// </vc-spec>
// <vc-code>
{
    var ar := ReversedArray(a);
    if HasIncreasingPair(ar) then
        var min_i := MinIndex(a, n);
        return n - min_i;
    else
        return 0;
}
// </vc-code>

