// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to properly prove array property and postcondition */
lemma ConsecutiveArrayLemma(s: array<int>, i: int)
    requires forall k, j :: 0 <= k < j < s.Length ==> s[k] <= s[j]
    requires forall k :: 0 <= k < s.Length ==> s[k] >= 0
    requires 0 <= i <= s.Length
    requires forall k :: 0 <= k < i ==> s[k] == k
    ensures i < s.Length ==> (s[i] != i ==> forall j :: 0 <= j < s.Length ==> s[j] != i)
    ensures i == s.Length ==> forall j :: 0 <= j < s.Length ==> s[j] != i
{
    if i < s.Length && s[i] != i {
        if s[i] > i {
            forall j | 0 <= j < s.Length
                ensures s[j] != i
            {
                if j < i {
                    assert s[j] == j;
                }
                if j >= i {
                    assert s[i] <= s[j];
                    assert i < s[i] <= s[j];
                }
            }
        } else {
            assert s[i] < i;
            if i > 0 {
                assert s[i-1] == i - 1;
                assert s[i-1] <= s[i];
                assert i - 1 <= s[i] < i;
                assert false;
            } else {
                assert s[0] >= 0;
                assert false;
            }
        }
    }
    if i == s.Length {
        forall j | 0 <= j < s.Length
            ensures s[j] != i
        {
            assert s[j] == j < i;
        }
    }
}

lemma AllValuesExistLemma(s: array<int>, v: int)
    requires forall k, j :: 0 <= k < j < s.Length ==> s[k] <= s[j]
    requires forall k :: 0 <= k < s.Length ==> s[k] >= 0
    requires forall k :: 0 <= k < v ==> s[k] == k
    requires v <= s.Length
    ensures forall k :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
{
    forall k | 0 <= k < v
        ensures exists j :: 0 <= j < s.Length && s[j] == k
    {
        assert s[k] == k;
    }
}
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariant and strengthened proof */
    if s.Length == 0 {
        v := 0;
        return;
    }
    
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall k :: 0 <= k < i ==> s[k] == k
        invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < s.Length && s[j] == k
    {
        if s[i] != i {
            ConsecutiveArrayLemma(s, i);
            AllValuesExistLemma(s, i);
            v := i;
            return;
        }
        i := i + 1;
    }
    
    ConsecutiveArrayLemma(s, s.Length);
    AllValuesExistLemma(s, s.Length);
    v := s.Length;
}
// </vc-code>
