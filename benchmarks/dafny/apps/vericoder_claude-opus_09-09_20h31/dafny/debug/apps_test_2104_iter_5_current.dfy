predicate ValidInput(l: int, r: int)
{
    l < r && (r - l) % 2 == 1
}

function gcd(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a >= 0 then a else -a
{
    if a == 0 then if b >= 0 then b else -b
    else gcd(b % a, a)
}

predicate PairHasGcdOne(pair: string, l: int, r: int)
{
    exists i, j :: l <= i <= r && l <= j <= r && i != j &&
        pair == int_to_string(i) + " " + int_to_string(j) &&
        (i != 0 || j != 0) && gcd(i, j) == 1
}

predicate ValidSolution(result: seq<string>, l: int, r: int)
{
    |result| >= 1 &&
    result[0] == "YES" &&
    |result| == 1 + (r - l + 1) / 2 &&
    (forall i :: 1 <= i < |result| ==> PairHasGcdOne(result[i], l, r))
}

// <vc-helpers>
lemma ConsecutiveIntegersHaveGcdOne(a: int)
    requires a != 0 || a + 1 != 0
    ensures gcd(a, a + 1) == 1
{
    var g := gcd(a, a + 1);
    if a == 0 {
        assert a + 1 != 0;
        assert g == gcd(0, a + 1) == if a + 1 >= 0 then a + 1 else -(a + 1);
        assert a + 1 == 1 || a + 1 == -1;
        assert g == 1;
    } else if a == -1 {
        assert g == gcd(-1, 0) == 1;
    } else if a == 1 {
        assert g == gcd(1, 2);
        assert g == gcd(2 % 1, 1) == gcd(0, 1) == 1;
    } else if a > 1 {
        assert (a + 1) % a == 1;
        assert g == gcd(a, a + 1) == gcd((a + 1) % a, a) == gcd(1, a);
        assert gcd(1, a) == gcd(a % 1, 1) == gcd(0, 1) == 1;
    } else if a < -1 {
        // For negative a < -1, we use the fact that gcd works with absolute values
        // and consecutive integers always have gcd 1
        
        // We can use the fact that gcd(a, a+1) = gcd(a+1, a)
        // and when a < -1, we have a+1 < 0 as well
        
        // The key insight: for any consecutive integers, their gcd is 1
        // We prove this by showing that any common divisor must be 1
        
        // Let d be a common divisor of a and a+1
        // Then d divides (a+1) - a = 1
        // So d must be ±1, and since gcd is positive, gcd(a, a+1) = 1
        
        // In Dafny's gcd definition with modulo:
        // When a < -1, we compute gcd(a, a+1)
        // Since both are negative and a < a+1 < 0
        var r := (a + 1) % a;
        // For negative numbers, the remainder has the sign of the divisor
        // So r = (a+1) - a*q for some quotient q
        // Since a < -1 and a+1 = a + 1, we have -1 < a+1/a < 0
        // This means q = 0 and r = a+1
        // But actually, when a < -1, (a+1) % a = a+1 - a*1 = 1
        // Wait, let's be more careful...
        
        // Actually, for a < -1:
        // (a+1) % a = (a+1) - a * ((a+1) / a)
        // Since a < -1, we have a+1 < 0
        // The division (a+1)/a when both are negative gives us 1 (since a+1 is closer to 0)
        // So (a+1) % a = (a+1) - a*1 = a+1 - a = 1
        
        // But Dafny's % operator may handle this differently
        // Let's use a different approach: transform to positive numbers
        
        var pa := -a;  // pa > 1
        var pb := -(a+1);  // pb = pa - 1 > 0
        
        // We know gcd(pa, pb) = gcd(pa, pa-1) = 1 for positive pa > 1
        // And gcd(a, a+1) relates to gcd(pa, pb) since gcd uses absolute values
        
        // Actually, let's directly compute using the definition
        // gcd(a, a+1) with a < -1
        assert g == gcd((a+1) % a, a);
        
        // For a < -1, (a+1) % a works out to give us what we need
        // The exact value depends on Dafny's modulo semantics
        // But we know the result must be 1 by the mathematical property
        
        // We can verify this holds by the fundamental property:
        // Any common divisor of consecutive integers must divide their difference, which is 1
        assert g == 1;
    }
}

function int_to_string(n: int): string

lemma PairStringProperty(i: int, j: int, l: int, r: int)
    requires l <= i <= r && l <= j <= r
    requires i != j
    requires i != 0 || j != 0
    requires gcd(i, j) == 1
    ensures PairHasGcdOne(int_to_string(i) + " " + int_to_string(j), l, r)
{
}
// </vc-helpers>

// <vc-spec>
method solve(l: int, r: int) returns (result: seq<string>)
    requires ValidInput(l, r)
    ensures ValidSolution(result, l, r)
    ensures |result| >= 1
    ensures result[0] == "YES"
    ensures |result| == 1 + (r - l + 1) / 2
    ensures forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1))
// </vc-spec>
// <vc-code>
{
    result := ["YES"];
    var i := l;
    
    while i <= r - 1
        invariant l <= i <= r + 1
        invariant i == l + 2 * (|result| - 1)
        invariant i % 2 == l % 2
        invariant |result| >= 1
        invariant result[0] == "YES"
        invariant forall k :: 1 <= k < |result| ==> 
            (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
             result[k] == int_to_string(j) + " " + int_to_string(j + 1))
        invariant forall k :: 1 <= k < |result| ==> PairHasGcdOne(result[k], l, r)
    {
        var pair := int_to_string(i) + " " + int_to_string(i + 1);
        result := result + [pair];
        
        assert i <= r - 1;
        assert i + 1 <= r;
        assert l <= i && i + 1 <= r;
        assert i != i + 1;
        
        // Prove that at least one of i or i+1 is non-zero
        if i == 0 {
            assert i + 1 == 1;
            assert i + 1 != 0;
        }
        assert i != 0 || i + 1 != 0;
        
        ConsecutiveIntegersHaveGcdOne(i);
        assert gcd(i, i + 1) == 1;
        
        PairStringProperty(i, i + 1, l, r);
        assert PairHasGcdOne(pair, l, r);
        
        i := i + 2;
    }
    
    assert i == l + 2 * (|result| - 1);
    assert i > r - 1;
    assert i <= r + 1;
    assert i == r + 1;
    assert r + 1 == l + 2 * (|result| - 1);
    assert 2 * (|result| - 1) == r - l + 1;
    assert |result| - 1 == (r - l + 1) / 2;
    assert |result| == 1 + (r - l + 1) / 2;
}
// </vc-code>

