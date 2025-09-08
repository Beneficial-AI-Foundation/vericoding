Given integers l and r where l < r, partition all integers from l to r (inclusive) 
into exactly (r-l+1)/2 pairs such that each pair (i,j) has gcd(i,j) = 1. 
Each number must appear in exactly one pair.

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

function int_to_string(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then pos_int_to_string(n)
    else "-" + pos_int_to_string(-n)
}

function pos_int_to_string(n: int): string
    requires n > 0
{
    if n < 10 then
        match n
        case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4" case 5 => "5"
        case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    else
        pos_int_to_string(n / 10) + 
        (if n % 10 == 0 then "0" else pos_int_to_string(n % 10))
}

lemma ConsecutiveGcdOne(a: int)
    ensures (a != 0 || (a + 1) != 0)
    ensures gcd(a, a + 1) == 1
{
    // Base cases
    if a == 0 {
        assert gcd(0, 1) == 1;
    } else if a == -1 {
        assert gcd(-1, 0) == 1;
    } else {
        // Use mathematical property that gcd(a, a+1) = gcd(a, 1) = 1
        // This follows from the fact that any common divisor of a and a+1
        // must also divide their difference, which is 1
        calc {
            gcd(a, a + 1);
        ==  { /* gcd(x,y) = gcd(x, y-x) when y > x > 0, or gcd(x,y) = gcd(x, y%x) */ }
            gcd(a, 1);
        ==  { /* gcd of any number with 1 is 1 */ }
            1;
        }
    }
}

method solve(l: int, r: int) returns (result: seq<string>)
    requires ValidInput(l, r)
    ensures ValidSolution(result, l, r)
    ensures |result| >= 1
    ensures result[0] == "YES"
    ensures |result| == 1 + (r - l + 1) / 2
    ensures forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1))
{
    var pairs := [];
    var i := l;
    while i <= r - 1
        invariant l <= i <= r + 1
        invariant i % 2 == l % 2
        invariant |pairs| == (i - l) / 2
        invariant forall k :: 0 <= k < |pairs| ==> 
            (var j := l + 2 * k; 
             l <= j <= r - 1 && j % 2 == l % 2 && 
             pairs[k] == int_to_string(j) + " " + int_to_string(j + 1))
        invariant forall k :: 0 <= k < |pairs| ==> 
            PairHasGcdOne(pairs[k], l, r)
    {
        ConsecutiveGcdOne(i);
        var tmpCall1 := int_to_string(i);
        var tmpCall2 := int_to_string(i + 1);
        var pair := tmpCall1 + " " + tmpCall2;
        
        // Help Dafny see that this pair has gcd 1
        assert pair == int_to_string(i) + " " + int_to_string(i + 1);
        assert PairHasGcdOne(pair, l, r);
        
        pairs := pairs + [pair];
        i := i + 2;
    }
    result := ["YES"] + pairs;
    
    // Help Dafny verify the postcondition
    assert result[0] == "YES";
    assert |result| == 1 + |pairs|;
    assert |pairs| == (r - l + 1) / 2;
    assert forall k :: 1 <= k < |result| ==> result[k] == pairs[k-1];
    assert forall k :: 0 <= k < |pairs| ==> PairHasGcdOne(pairs[k], l, r);
}
