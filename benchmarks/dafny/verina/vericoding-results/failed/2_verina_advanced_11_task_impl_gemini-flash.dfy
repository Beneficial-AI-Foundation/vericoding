// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unused helper function */
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
    if lst.Length == 0 {
        return -1;
    }

    var candidate := lst[0];
    var count := 0;

    for i := 0 to lst.Length
        invariant 0 <= i <= lst.Length
        invariant i > 0 ==> (count == 0 && candidate != lst[i-1] ==> CountOccurrences(candidate, lst[..i]) == CountOccurrences(candidate, lst[..i-1]))
        invariant i > 0 ==> (count == 0 && candidate == lst[i-1] ==> CountOccurrences(candidate, lst[..i]) == CountOccurrences(candidate, lst[..i-1]) + 1)
        invariant i > 0 ==> (count != 0 ==> CountOccurrences(candidate, lst[..i]) == count + CountOccurrences(candidate, lst[..(i-1)]))
        invariant i >= 0 ==> (count >= 0 && (i == 0 || i > 0 && !(count == 0 && candidate != lst[i-1]))) // This invariant should prevent count from being negative and ensure candidate is tracked correctly even when count is zero.


    {
        if count == 0 {
            candidate := lst[i];
            count := 1;
        } else if lst[i] == candidate {
            count := count + 1;
        } else {
            count := count - 1;
        }
    }
    
    count := 0;
    for i := 0 to lst.Length
        invariant 0 <= i <= lst.Length
        invariant count == CountOccurrences(candidate, lst[..i])

    {
        if i < lst.Length && lst[i] == candidate {
            count := count + 1;
        }
    }

    if count * 2 > lst.Length {
        result := candidate;
    } else {
        result := -1;
    }
}
// </vc-code>
