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
function int_to_string_nonneg(i: int): string
    requires i >= 0
    decreases i
{
    if i == 0 then "0"
    else if i < 10 then ["0","1","2","3","4","5","6","7","8","9"][i]
    else int_to_string_nonneg(i/10) + int_to_string_nonneg(i%10)
}

function int_to_string(i: int): string
{
    if i < 0 then "-" + int_to_string_nonneg(-i)
    else int_to_string_nonneg(i)
}

lemma gcd_one_for_consecutive(a: int, b: int)
    requires a != b
    requires b == a + 1 || a == b + 1
    requires a != 0 || b != 0
    ensures gcd(a, b) == 1
{
    if b < a {
        gcd_one_for_consecutive(b, a);
    } else if a < 0 {
        calc == {
            gcd(a, b);
            gcd(b % a, a);
            gcd((a+1) % a, a);
            gcd(1, a);
            gcd(0, 1);
            1;
        }
    } else if a == 0 {
        assert b == 1;
        calc == {
            gcd(0, 1);
            1;
        }
    } else {
        calc == {
            gcd(a, a+1);
            gcd((a+1) % a, a);
            gcd(1, a);
            gcd(0, 1);
            1;
        }
    }
}
// </vc-helpers>
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
    while j <= r-1
        invariant l <= j <= r+1
        invariant j % 2 == l % 2
        invariant |result| == 1 + (j - l) / 2
        invariant forall i :: 1 <= i < |result| ==> 
            result[i] == int_to_string(l + 2*(i-1)) + " " + int_to_string(l + 2*(i-1)+1)
    {
        result := result + [int_to_string(j) + " " + int_to_string(j+1)];
        assert gcd(j, j+1) == 1 by {
            gcd_one_for_consecutive(j, j+1);
        }
        j := j + 2;
    }
}
// </vc-code>
// </vc-code>

