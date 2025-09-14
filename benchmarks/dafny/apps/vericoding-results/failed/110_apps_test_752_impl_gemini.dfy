predicate validInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    |lines| >= 1 && 
    (var n := parseInteger(lines[0]);
     n >= 0 && |lines| >= 2*n + 1 && 
     (forall i :: 1 <= i <= 2*n ==> i < |lines| && |lines[i]| > 0))
}

function computeMismatches(stdin_input: string): nat
    requires validInput(stdin_input)
    ensures computeMismatches(stdin_input) <= parseInteger(splitLines(stdin_input)[0])
{
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    if n == 0 then 0
    else
        var prevSizes := countSizes(lines[1..n+1]);
        var currentSizes := lines[n+1..2*n+1];
        countUnmatchedSizes(prevSizes, currentSizes)
}

// <vc-helpers>
function sumMapValues(m: map<nat, nat>): nat
{
  if m == map[] then 0
  else
    var k :| k in m.Keys;
    m[k] + sumMapValues(m - {k})
}

lemma lemma_totalCount(strings: seq<string>)
  ensures sumMapValues(countSizes(strings)) == |strings|
  decreases |strings|
{
  if |strings| == 0 {
    // Base case: sum of values in an empty map is 0, same as length of empty sequence.
  } else {
    var car := strings[0];
    var cdr := strings[1..];
    var rest_counts := countSizes(cdr);
    lemma_totalCount(cdr); //
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n' || (|result| > 1 && result[|result|-2..] == "\r\n")
    ensures exists mismatches: nat :: result == intToString(mismatches) + "\n" && 
            mismatches == computeMismatches(stdin_input)
    ensures (var lines := splitLines(stdin_input);
             var n := parseInteger(lines[0]);
             n >= 0 ==> (var mismatches := computeMismatches(stdin_input);
                        mismatches <= n &&
                        result == intToString(mismatches) + "\n"))
// </vc-spec>
// <vc-code>
function sumMapValues(m: map<nat, nat>): nat
{
  if m == map[] then 0
  else
    var k :| k in m.Keys;
    m[k] + sumMapValues(m - {k})
}

lemma lemma_totalCount(strings: seq<string>)
  ensures sumMapValues(countSizes(strings)) == |strings|
  decreases |strings|
{
  if |strings| == 0 {
    // Base case: sum of values in an empty map is 0, same as length of empty sequence.
  } else {
    var car := strings[0];
    var cdr := strings[1..];
    var rest_counts := countSizes(cdr);
    lemma_totalCount(cdr); //
// </vc-code>

