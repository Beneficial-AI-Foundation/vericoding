predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
}

function countChar(s: string, c: char): nat
{
    |set i | 0 <= i < |s| && s[i] == c|
}

predicate ValidOutput(s: string, result: string)
    requires ValidInput(s)
{
    var countX := countChar(s, 'x');
    var countY := countChar(s, 'y');
    if countY > countX then
        |result| == countY - countX && forall i :: 0 <= i < |result| ==> result[i] == 'y'
    else
        |result| == countX - countY && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
function method Replicate(c: char, n: nat): string
    ensures |Replicate(c, n)| == n
    ensures forall i :: 0 <= i < n ==> Replicate(c, n)[i] == c
{
    if n == 0 then ""
    else Replicate(c, n-1) + [c]
}

method ComputeCount(s: string, c: char) returns (count: nat)
    ensures count == countChar(s, c)
{
    var n: nat := 0;
    for i := 0 to |s|
        invariant n == countChar(s[0..i], c)
    {
        if s[i] == c {
            n := n + 1;
        }
    }
    count := n;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    var countX := ComputeCount(s, 'x');
    var countY := ComputeCount(s, 'y');
    if countY > countX {
        result := Replicate('y', (countY - countX) as nat);
    } else {
        result := Replicate('x', (countX - countY) as nat);
    }
}
// </vc-code>

