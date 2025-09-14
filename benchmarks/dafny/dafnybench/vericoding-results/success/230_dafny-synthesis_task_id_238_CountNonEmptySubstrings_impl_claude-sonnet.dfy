

// <vc-helpers>
lemma SubstringCountFormula(n: nat)
    ensures n * (n + 1) / 2 == if n == 0 then 0 else n + (n - 1) * n / 2
{
    if n == 0 {
        assert n * (n + 1) / 2 == 0;
    } else {
        calc {
            n * (n + 1) / 2;
            ==
            (n * n + n) / 2;
            == { assert n * n + n == n + n * n; }
            (n + n * n) / 2;
        }
    }
}

lemma CountInvariant(s: string, i: nat, currentCount: int)
    requires i <= |s|
    requires currentCount == i * (i + 1) / 2
    ensures currentCount + (|s| - i) == (|s| - i) + i * (i + 1) / 2
{
}

lemma LoopInvariantMaintained(i: nat)
    ensures (i * (i + 1) / 2) + (i + 1) == (i + 1) * (i + 2) / 2
{
    calc {
        (i * (i + 1) / 2) + (i + 1);
        ==
        (i * (i + 1) + 2 * (i + 1)) / 2;
        ==
        ((i + 2) * (i + 1)) / 2;
        ==
        (i + 1) * (i + 2) / 2;
    }
}
// </vc-helpers>

// <vc-spec>
method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == i * (i + 1) / 2
    {
        count := count + (i + 1);
        i := i + 1;
        
        LoopInvariantMaintained(i - 1);
        assert count == i * (i + 1) / 2;
    }
    
    assert i == |s|;
    assert count == |s| * (|s| + 1) / 2;
}
// </vc-code>

