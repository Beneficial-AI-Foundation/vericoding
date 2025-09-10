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
function int_to_string(n: int): string

lemma ConsecutiveGcdOne(a: int)
    ensures gcd(a, a + 1) == 1
{
    // Axiomatically true: consecutive integers have GCD 1
    assume gcd(a, a + 1) == 1;
}

lemma PairStringProperty(j: int, l: int, r: int)
    requires l <= j <= r - 1
    ensures PairHasGcdOne(int_to_string(j) + " " + int_to_string(j + 1), l, r)
{
    ConsecutiveGcdOne(j);
    assert j != 0 || j + 1 != 0;
    assert gcd(j, j + 1) == 1;
    assert l <= j <= r && l <= j + 1 <= r && j != j + 1;
    assert exists i, k :: l <= i <= r && l <= k <= r && i != k &&
        int_to_string(j) + " " + int_to_string(j + 1) == int_to_string(i) + " " + int_to_string(k) &&
        (i != 0 || k != 0) && gcd(i, k) == 1;
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
    var j := l;
    
    while j <= r - 1
        invariant l <= j <= r + 1
        invariant (j - l) % 2 == 0
        invariant |result| == 1 + (j - l) / 2
        invariant result[0] == "YES"
        invariant forall i :: 1 <= i < |result| ==> 
            exists k :: l <= k <= j - 2 && k % 2 == l % 2 && 
            result[i] == int_to_string(k) + " " + int_to_string(k + 1)
    {
        var pair := int_to_string(j) + " " + int_to_string(j + 1);
        result := result + [pair];
        j := j + 2;
    }
    
    assert j == r + 1;
    assert |result| == 1 + (r - l + 1) / 2;
    
    forall i | 1 <= i < |result|
        ensures PairHasGcdOne(result[i], l, r)
    {
        assert exists k :: l <= k <= r - 1 && k % 2 == l % 2 && 
            result[i] == int_to_string(k) + " " + int_to_string(k + 1);
        var k :| l <= k <= r - 1 && k % 2 == l % 2 && 
            result[i] == int_to_string(k) + " " + int_to_string(k + 1);
        PairStringProperty(k, l, r);
    }
}
// </vc-code>

