predicate validInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate validOutput(output: string, input: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

predicate correctIncrementalQueryProcessing(input: string, output: string)
{
    true
}

function splitLinesFunc(input: string): seq<string>
{
    if |input| == 0 then [] else ["1", "query1"]
}

predicate isValidInteger(s: string)
{
    |s| > 0
}

function countType2Queries(queries: seq<string>): nat
{
    0
}

function intToString(x: int): string
{
    "1"
}

// <vc-helpers>
lemma LineCountLemma(input: string, queries: seq<string>)
  requires |input| > 0
  requires input[|input|-1] == '\n'
  requires queries == splitLinesFunc(input)
  ensures |queries| > 0
{
  // Axiomatic lemma - no body needed
}

lemma CountType2Valid(queries: seq<string>)
  ensures countType2Queries(queries) >= 0
{
  // Axiomatic lemma - no body needed
}

lemma ValidateResults(n: nat, queries: seq<string>)
  requires n == countType2Queries(queries)
  ensures isValidInteger(intToString(n))
{
  // Type 2 queries count is always a natural number,
  // which intToString can handle and produce a valid integer string
}

lemma SplitLinesHelper(input: string)
  requires |input| > 0
  requires input[|input|-1] == '\n'
  ensures |splitLinesFunc(input)| > 0
{
  // Split result is guaranteed to have at least one element
}

lemma FinalNewLineLemma(s: string, n: nat)
  requires |s| > 0
  requires isValidInteger(s)
  ensures |s + "\n"| > 0 && (s + "\n")[|s + "\n"|-1] == '\n'
{
  // Adding newline to non-empty string preserves validity
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires validInput(input)
    ensures validOutput(output, input)
    ensures |output| > 0 && output[|output|-1] == '\n'
    ensures correctIncrementalQueryProcessing(input, output)
// </vc-spec>
// <vc-code>
{
  var queries := splitLinesFunc(input);
  SplitLinesHelper(input);
  
  var count := countType2Queries(queries);
  CountType2Valid(queries);
  
  var resultStr := intToString(count);
  ValidateResults(count, queries);
  
  FinalNewLineLemma(resultStr, count);
  output := resultStr + "\n";
  assert |output| > 0 && output[|output|-1] == '\n';
}
// </vc-code>

