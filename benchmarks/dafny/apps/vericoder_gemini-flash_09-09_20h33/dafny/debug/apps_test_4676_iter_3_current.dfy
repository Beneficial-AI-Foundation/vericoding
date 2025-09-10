predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    (a == b || a == b + 1) &&
    (a > 0 || b == 0)
}

function GetO(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[0]
}

function GetE(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[1]
}

function CorrectResult(input: string): string
    requires ValidInput(input)
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;
    if a == b then
        InterleaveEqual(O, E)
    else
        InterleaveUnequal(O, E)
}

function InterleaveEqual(O: string, E: string): string
    requires |O| == |E|
{
    if |O| == 0 then ""
    else [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
}

function InterleaveUnequal(O: string, E: string): string
    requires |O| == |E| + 1
{
    if |E| == 0 then O
    else [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..])
}

// <vc-helpers>
function split(s: string, sep: char): seq<string>
  reads K
  ensures forall i :: 0 <= i < |split(s, sep)| ==> split(s, sep)[i] in s
  decreases |s|
{
  if sep !in s then [s]
  else
    var i := 0;
    while i < |s| && s[i] != sep
      invariant 0 <= i <= |s|
      invariant !sep in s[..i]
      decreases |s| - i
    {
      i := i + 1;
    }
    if i == |s| then
      [s]
    else
      [s[..i]] + split(s[i+1..], sep)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectResult(input)
// </vc-spec>
// <vc-code>
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;

    if a == b {
        result := InterleaveEqual(O, E);
    } else {
        result := InterleaveUnequal(O, E);
    }
}
// </vc-code>

