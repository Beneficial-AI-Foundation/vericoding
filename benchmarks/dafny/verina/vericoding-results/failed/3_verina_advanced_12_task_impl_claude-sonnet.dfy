// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FirstDuplicate(lst: seq<int>) returns (result: int)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
            forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error by removing extra semicolon */
    result := -1;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant result == -1 ==> forall k, l :: 0 <= k < l < i ==> lst[k] != lst[l]
        invariant result != -1 ==> exists k, l :: 0 <= k < l < i && lst[k] == lst[l] && lst[k] == result && forall m, n :: 0 <= m < n < i && lst[m] == lst[n] && n <= k ==> m >= k
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant result == -1 ==> forall k :: 0 <= k < j ==> lst[k] != lst[i]
            invariant result != -1 ==> exists k, l :: 0 <= k < l < i && lst[k] == lst[l] && lst[k] == result && forall m, n :: 0 <= m < n < i && lst[m] == lst[n] && n <= k ==> m >= k
        {
            if lst[j] == lst[i] {
                result := lst[i];
                assert 0 <= j < i < |lst| && lst[j] == lst[i] && lst[j] == result;
                assert forall m, n :: 0 <= m < n < |lst| && lst[m] == lst[n] && n <= j ==> m >= j by {
                    forall m, n | 0 <= m < n < |lst| && lst[m] == lst[n] && n <= j
                        ensures m >= j
                    {
                        if n <= j {
                            if n < j {
                                assert 0 <= m < n < i;
                                assert lst[m] == lst[n];
                                assert false;
                            } else {
                                assert n == j;
                                if m < j {
                                    assert lst[m] == lst[j] == lst[i];
                                    assert 0 <= m < j < i;
                                    assert false;
                                }
                            }
                        }
                    }
                };
                assert exists k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && lst[k] == result && forall m, n :: 0 <= m < n < |lst| && lst[m] == lst[n] && n <= k ==> m >= k by {
                    assert 0 <= j < i < |lst| && lst[j] == lst[i] && lst[j] == result;
                }
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    assert forall k, l :: 0 <= k < l < |lst| ==> lst[k] != lst[l];
}
// </vc-code>
