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
        if a + 1 == 1 {
            assert g == 1;
        } else if a + 1 == -1 {
            assert g == 1;
        }
    } else if a == -1 {
        assert g == gcd(-1, 0) == 1;
    } else {
        assert g == gcd(a, a + 1);
        assert (a + 1) % a == 1 || (a + 1) % a == 1 - a;
        if a > 0 {
            assert (a + 1) % a == 1;
            assert g == gcd(1, a);
            assert g == gcd(1, a) == gcd(a % 1, 1) == gcd(0, 1) == 1;
        } else if a < -1 {
            assert (a + 1) % a == a + 1;
            assert g == gcd(a + 1, a);
            var g' := gcd(1, -a);
            assert g' == 1;
        }
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
            exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
            result[k] == int_to_string(j) + " " + int_to_string(j + 1)
    {
        var pair := int_to_string(i) + " " + int_to_string(i + 1);
        result := result + [pair];
        
        ConsecutiveIntegersHaveGcdOne(i);
        assert i != 0 || i + 1 != 0;
        assert gcd(i, i + 1) == 1;
        PairStringProperty(i, i + 1, l, r);
        assert PairHasGcdOne(pair, l, r);
        
        i := i + 2;
    }
    
    assert |result| == 1 + (r - l + 1) / 2;
}
// </vc-code>

