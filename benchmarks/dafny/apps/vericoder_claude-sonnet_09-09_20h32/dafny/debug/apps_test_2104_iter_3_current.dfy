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

lemma ConsecutiveGcdOne(a: int, b: int)
    requires b == a + 1
    requires a != 0 || b != 0
    ensures gcd(a, b) == 1
{
    if a == 0 {
        assert b == 1;
    } else if a > 0 {
        assert (a + 1) % a == 1;
    } else {
        assert a < 0;
        assert (a + 1) % a == 1;
    }
}

lemma PairValidation(j: int, l: int, r: int)
    requires l <= j <= r - 1
    requires j + 1 <= r
    requires (j != 0 || j + 1 != 0)
    ensures PairHasGcdOne(int_to_string(j) + " " + int_to_string(j + 1), l, r)
{
    ConsecutiveGcdOne(j, j + 1);
    assert l <= j <= r && l <= j + 1 <= r && j != j + 1;
    assert gcd(j, j + 1) == 1;
}

lemma CountingLemma(l: int, r: int, current: int)
    requires ValidInput(l, r)
    requires l <= current
    requires current % 2 == l % 2
    requires current > r - 1
    ensures 1 + (current - l) / 2 == 1 + (r - l + 1) / 2
{
    assert current >= r + 1;
    assert current % 2 == l % 2;
    assert (r - l) % 2 == 1;
    if l % 2 == r % 2 {
        assert current >= r + 2;
    } else {
        assert current >= r + 1;
        assert current == r + 1;
    }
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
    var current := l;
    
    while current <= r - 1
        invariant l <= current
        invariant current % 2 == l % 2
        invariant |result| == 1 + (current - l) / 2
        invariant result[0] == "YES"
        invariant forall i :: 1 <= i < |result| ==> 
            (exists j :: l <= j <= current - 2 && j % 2 == l % 2 && 
             result[i] == int_to_string(j) + " " + int_to_string(j + 1))
        invariant forall i :: 1 <= i < |result| ==> PairHasGcdOne(result[i], l, r)
    {
        var pair := int_to_string(current) + " " + int_to_string(current + 1);
        PairValidation(current, l, r);
        result := result + [pair];
        current := current + 2;
    }
    
    CountingLemma(l, r, current);
    
    assert forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1));
}
// </vc-code>

