function count_a(s: string): int
    ensures count_a(s) >= 0
    ensures count_a(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'a' then 1 else 0) + count_a(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidInput(s: string)
{
    |s| >= 1 && exists i :: 0 <= i < |s| && s[i] == 'a'
}

predicate IsGoodString(s: string)
{
    |s| > 0 && count_a(s) > |s| / 2
}

// <vc-helpers>
lemma CountAThenGoodString(s: string)
    requires ValidInput(s)
    ensures IsGoodString(s) || (2 * count_a(s) - 1 <= |s|)
{
    //Proof by case analysis on count_a(s) > |s| / 2
    if count_a(s) > |s| / 2  {
        assert IsGoodString(s);
    } else {
        assert 2 * count_a(s) <= |s|;
        assert 2 * count_a(s) - 1 <= |s| - 1;
        assert 2 * count_a(s) - 1 <= |s|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 1
    ensures result <= |s|
    ensures result == min(2 * count_a(s) - 1, |s|)
// </vc-spec>
// <vc-code>
{
    var num_a := count_a(s);
    
    // Prove that result is at least 1
    // From ValidInput, we know |s| >= 1 and there exists at least one 'a'.
    // Therefore, num_a (count_a(s)) must be at least 1.
    assert num_a >= 1; 

    // Calculate `val` based on the formula, which applies regardless of IsGoodString(s)
    var val := 2 * num_a - 1;

    // Use the lemma to establish the relationship between IsGoodString(s) and val vs |s|
    CountAThenGoodString(s);

    if IsGoodString(s) {
        // If IsGoodString(s) is true, then count_a(s) > |s| / 2, which implies 2 * count_a(s) > |s|.
        // So, 2 * count_a(s) - 1 >= |s| (since integers).
        // In this case, min(2 * count_a(s) - 1, |s|) should be |s|.
        assert 2 * num_a - 1 >= |s|; // This is true because 2 * num_a > |s| means 2 * num_a >= |s| + 1, so 2 * num_a - 1 >= |s|.
        result := |s|; 
    } else {
        // If !IsGoodString(s), then count_a(s) <= |s| / 2.
        // This implies 2 * count_a(s) <= |s|.
        // So, 2 * count_a(s) - 1 < |s|.
        // In this case, min(2 * count_a(s) - 1, |s|) should be 2 * count_a(s) - 1.
        assert 2 * num_a - 1 < |s|; // This is true because 2 * num_a <= |s| means 2 * num_a - 1 < |s|.
        result := val;
    }

    assert result >= 1;
    assert result <= |s|;
    assert result == min(val, |s|);
}
// </vc-code>

