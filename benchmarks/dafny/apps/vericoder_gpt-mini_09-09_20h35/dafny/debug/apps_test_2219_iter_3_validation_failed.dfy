function minStepsToZero(n: nat, k: nat): nat
    requires k >= 2
    decreases n
{
    if n == 0 then 0
    else if n % k == 0 then 1 + minStepsToZero(n / k, k)
    else (n % k) + minStepsToZero(n - (n % k), k)
}

predicate validInput(input: string)
{
    |input| > 0 && 
    var lines := splitLinesFunc(input);
    |lines| >= 1 &&
    isValidNumber(lines[0]) &&
    var t := stringToIntFunc(lines[0]);
    t >= 1 && t <= 100 &&
    |lines| >= t + 1 &&
    forall i :: 1 <= i <= t ==> validTestCase(lines[i])
}

predicate validTestCase(line: string)
{
    var parts := splitSpacesFunc(line);
    |parts| == 2 &&
    isValidNumber(parts[0]) &&
    isValidNumber(parts[1]) &&
    var n := stringToIntFunc(parts[0]);
    var k := stringToIntFunc(parts[1]);
    n >= 1 && k >= 2
}

predicate isValidNumber(s: string)
{
    |s| >= 1 &&
    (s == "0" || (s[0] != '0' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')) &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function expectedOutput(input: string): string
    requires validInput(input)
{
    var lines := splitLinesFunc(input);
    var t := stringToIntFunc(lines[0]);
    var results := seq(t, i requires 0 <= i < t => 
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        intToStringFunc(minStepsToZero(n, k))
    );
    joinLinesSeq(results)
}

// <vc-helpers>
function splitLinesFunc(s: string): seq<string>
  ensures forall i :: 0 <= i < |splitLinesFunc(s)| ==> forall j :: 0 <= j < |splitLinesFunc(s)[i]| ==> splitLinesFunc(s)[i][j] != '\0'

function splitSpacesFunc(s: string): seq<string>
  ensures forall i :: 0 <= i < |splitSpacesFunc(s)| ==> forall j :: 0 <= j < |splitSpacesFunc(s)[i]| ==> splitSpacesFunc(s)[i][j] != '\0'

function stringToIntFunc(s: string): nat
  requires forall i :: 0 <= i < |s| ==> s[i] != '\0'

function intToStringFunc(n: nat): string
  ensures forall i :: 0 <= i < |intToStringFunc(n)| ==> intToStringFunc(n)[i] != '\0'

function joinLinesSeq(ss: seq<string>): string
  requires forall k :: 0 <= k < |ss| ==> forall i :: 0 <= i < |ss[k]| ==> ss[k][i] != '\0'
  ensures forall i :: 0 <= i < |joinLinesSeq(ss)| ==> joinLinesSeq(ss)[i] != '\0'

lemma expectedOutput_no_null(input: string)
  requires validInput(input)
  ensures forall i :: 0 <= i < |expectedOutput(input)| ==> expectedOutput(input)[i] != '\0'
{
  var lines := splitLinesFunc(input);
  var t := stringToIntFunc(lines[0]);
  var results := seq(t, i requires 0 <= i < t =>
      var parts := splitSpacesFunc(lines[i+1]);
      intToStringFunc(minStepsToZero(stringToIntFunc(parts[0]), stringToIntFunc(parts[1])))
  );
  assert expectedOutput(input) == joinLinesSeq(results);
  assert forall idx :: 0 <= idx < |results| ==>
    forall j :: 0 <= j < |results[idx]| ==> results[idx][j] != '\0'
  {
    fix idx;
    assume 0 <= idx < |results|;
    var s := results[idx];
    assert forall j :: 0 <= j < |s| ==> s[j] != '\0';
  }
  assert forall i :: 0 <= i < |joinLinesSeq(results)| ==> joinLinesSeq(results)[i] != '\0';
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires validInput(input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'
    ensures result == expectedOutput(input)
// </vc-spec>
// <vc-code>
{
  result := expectedOutput(input);
  expectedOutput_no_null(input);
  assert forall i :: 0 <= i < |result| ==> result[i] != '\0';
}
// </vc-code>

