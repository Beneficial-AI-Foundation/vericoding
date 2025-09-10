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
function int_to_string(x: int): string
    decreases if x >= 0 then x else -x + 1
{
    if x == 0 then "0"
    else if x < 0 then "-" + int_to_string(-x)
    else if x < 10 then [ "0", "1", "2", "3", "4", "5", "6", "7", "8", "9" ][x]
    else int_to_string(x / 10) + [ "0", "1", "2", "3", "4", "5","6","7","8","9" ][x % 10]
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
    var res: seq<string> := ["YES"];
    var j := l;
    while j <= r - 1 
        invariant 1 <= |res|
        invariant res[0] == "YES"
        invariant |res| == 1 + (j - l) / 2
        invariant l <= j <= r - 1 + 2
        invariant j % 2 == l % 2
        invariant forall i :: 1 <= i < |res| ==> PairHasGcdOne(res[i], l, r)
        invariant forall i :: 1 <= i < |res| ==> 
            (exists jj :: l <= jj <= r - 1 && jj % 2 == l % 2 && 
             res[i] == int_to_string(jj) + " " + int_to_string(jj + 1))
        decreases r - j + 1
    {
        var pair := int_to_string(j) + " " + int_to_string(j + 1);
        assert gcd(j, j + 1) == 1;
        res := res + [pair];
        j := j + 2;
    }
    result := res;
}
// </vc-code>

