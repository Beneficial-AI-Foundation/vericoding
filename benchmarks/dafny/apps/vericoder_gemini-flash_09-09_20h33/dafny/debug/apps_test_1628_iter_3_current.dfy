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
function createString(length: nat, c: char): string
  ensures |createString(length, c)| == length
  ensures forall i :: 0 <= i < length ==> createString(length, c)[i] == c
{
  if length == 0 then
    ""
  else
    c + createString(length - 1 as nat, c)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    var countX := countChar(s, 'x');
    var countY := countChar(s, 'y');

    if countY > countX then
        result := createString(countY - countX, 'y');
    else
        result := createString(countX - countY, 'x');
}
// </vc-code>

