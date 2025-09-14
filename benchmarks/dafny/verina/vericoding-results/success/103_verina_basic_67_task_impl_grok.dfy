// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
{
    result := true;
    var i: int := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant result == (forall k :: 0 <= k < i ==> x[k] == x[|x| - 1 - k])
    {
        if x[i] != x[|x| - 1 - i] {
            result := false;
        }
        i := i + 1;
    }
}
// </vc-code>
