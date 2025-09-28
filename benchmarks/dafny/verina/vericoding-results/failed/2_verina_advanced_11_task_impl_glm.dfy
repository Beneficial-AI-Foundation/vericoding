// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
lemma AtMostOneMajority(lst: seq<int>)
    ensures forall x, y :: 
        (CountOccurrences(x, lst) > |lst|/2 && CountOccurrences(y, lst) > |lst|/2) ==> x == y
{
    var n := |lst|;
    forall x, y | CountOccurrences(x, lst) > n/2 && CountOccurrences(y, lst) > n/2
        ensures x == y
    {
        if x != y {
            var Sx := set i | 0 <= i < n && lst[i] == x;
            var Sy := set i | 0 <= i < n && lst[i] == y;
            assert Sx !! Sy;
            assert |Sx union Sy| == |Sx| + |Sy|;
            assert |Sx union Sy| <= n;
            assert |Sx| >= n/2 + 1;
            assert |Sy| >= n/2 + 1;
            assert |Sx| + |Sy| >= 2 * (n/2 + 1);
            if n % 2 == 0 {
                assert 2 * (n/2 + 1) == n + 2;
            } else {
                assert 2 * (n/2) == n - 1;
                assert 2 * (n/2 + 1) == n - 1 + 2 == n + 1;
            }
            assert 2*(n/2+1) > n;
            assert |Sx| + |Sy| > n;
            assert |Sx| + |Sy| <= n;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
{
    var n := lst.Length;
    if n == 0 {
        return -1;
    }
    var lst_seq := lst[..];
    AtMostOneMajority(lst_seq);
    var distinct := set x | x in lst_seq;
    var xs := distinct.Elements;
    for i := 0 to |xs|-1
        invariant forall j :: 0 <= j < i ==> CountOccurrences(xs[j], lst_seq) <= n/2
    {
        var x := xs[i];
        if CountOccurrences(x, lst_seq) > n / 2 then
            return x;
    }
    return -1;
}
// </vc-code>
