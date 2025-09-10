predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
function IntToString(n: int): string
    requires 0 <= n <= 23
    ensures |IntToString(n)| == 1 || |IntToString(n)| == 2
{
    if n < 10 then [n as char] else ['0' + n/10, '0' + n%10]
}

lemma ValidInputExtractValues(input: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
        (input == IntToString(A) + " " + IntToString(B) + "\n" ||
         input == IntToString(A) + " " + IntToString(B))
{
}

function ExtractA(input: string): int
    requires |input| > 0
    requires ValidInput(input)
    ensures 0 <= ExtractA(input) <= 23
{
    var i := 0;
    var numStr := "";
    while i < |input| && input[i] != ' ' 
        invariant 0 <= i <= |input|
        invariant numStr == input[0..i]
        decreases |input| - i
    {
        numStr := numStr + [input[i]];
        i := i + 1;
    }
    ParseInt(numStr)
}

function ExtractB(input: string): int
    requires |input| > 0
    requires ValidInput(input)
    ensures 0 <= ExtractB(input) <= 23
{
    var i := 0;
    while i < |input| && input[i] != ' ' 
        invariant 0 <= i <= |input|
        decreases |input| - i
    {
        i := i + 1;
    }
    i := i + 1;
    var numStr := "";
    while i < |input| && input[i] != '\n' && input[i] != ' '
        invariant i <= |input|
        invariant numStr == input[i-|numStr|..i]
        decreases |input| - i
    {
        numStr := numStr + [input[i]];
        i := i + 1;
    }
    ParseInt(numStr)
}

function ParseInt(s: string): int
    requires |s| > 0 && (|s| == 1 || |s| == 2)
    requires forall i :: 0 <= i < |s| ==> s[i] in ['0'..'9']
    ensures 0 <= ParseInt(s) <= 99
{
    if |s| == 1 then s[0] - '0' else (s[0] - '0') * 10 + (s[1] - '0')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
  var A := ExtractA(input);
  var B := ExtractB(input);
  
  assert 0 <= A <= 23;
  assert 0 <= B <= 23;
  
  var time := (A + B) % 24;
  
  assert 0 <= time <= 23;
  
  if time < 10 then {
    result := [('0' + time) as char] + "\n";
  } else {
    result := [('0' + time / 10) as char] + [('0' + time % 10) as char] + "\n";
  }
}
// </vc-code>

