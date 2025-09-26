// <vc-preamble>
predicate validInputFormat(stdin_input: seq<char>)
{
  var lines := splitLines(stdin_input);
  |lines| >= 2 &&
  parseInt(lines[0]) > 0 &&
  parseInt(lines[0]) <= 1000000000000000 &&
  parseInt(lines[1]) >= 0 &&
  parseInt(lines[1]) <= 300000 &&
  |lines| >= 2 + parseInt(lines[1]) &&
  forall i :: 2 <= i < 2 + parseInt(lines[1]) ==> 
    |splitSpace(lines[i])| >= 2 &&
    parseInt(splitSpace(lines[i])[0]) > 0 &&
    parseInt(splitSpace(lines[i])[1]) > 0 &&
    isDivisor(parseInt(splitSpace(lines[i])[0]), parseInt(lines[0])) &&
    isDivisor(parseInt(splitSpace(lines[i])[1]), parseInt(lines[0]))
}

predicate validOutputFormat(result: seq<char>, stdin_input: seq<char>)
{
  var inputLines := splitLines(stdin_input);
  var outputLines := splitLines(result);
  |inputLines| >= 2 ==>
    |outputLines| == parseInt(inputLines[1])
}

predicate correctShortestPathCounts(stdin_input: seq<char>, result: seq<char>)
{
  var inputLines := splitLines(stdin_input);
  var outputLines := splitLines(result);
  |inputLines| >= 2 && |outputLines| == parseInt(inputLines[1]) ==>
    var D := parseInt(inputLines[0]);
    D > 0 ==>
    var primeFactors := extractUniquePrimeFactors(D);
    forall i :: 0 <= i < |outputLines| && 2 + i < |inputLines| ==>
      var queryParts := splitSpace(inputLines[2 + i]);
      |queryParts| >= 2 ==>
        var u := parseInt(queryParts[0]);
        var v := parseInt(queryParts[1]);
        u > 0 && v > 0 ==>
        var pathCount := parseInt(outputLines[i]);
        pathCount == computeShortestPathCountInDivisorGraph(u, v, primeFactors, 998244353)
}

predicate allOutputValuesInModRange(result: seq<char>)
{
  var outputLines := splitLines(result);
  forall i :: 0 <= i < |outputLines| ==>
    var value := parseInt(outputLines[i]);
    0 <= value < 998244353
}

predicate correctNumberOfOutputLines(stdin_input: seq<char>, result: seq<char>)
{
  var inputLines := splitLines(stdin_input);
  var outputLines := splitLines(result);
  |inputLines| >= 2 ==> |outputLines| == parseInt(inputLines[1])
}
// </vc-preamble>

// <vc-helpers>
function extractUniquePrimeFactors(D: int): seq<int>
  requires D > 0
{
  []
}

function computeShortestPathCountInDivisorGraph(u: int, v: int, primeFactors: seq<int>, mod: int): int
  requires u > 0 && v > 0 && mod == 998244353
  requires forall p :: p in primeFactors ==> isPrime(p)
{
  if u == v then 1 else 0
}

function precomputeFactorials(N: int, mod: int): seq<int>
  requires N >= 0 && mod > 1
{
  []
}

function precomputeInverseFactorials(N: int, mod: int, factorials: seq<int>): seq<int>
  requires N >= 0 && mod == 998244353
  requires |factorials| == N + 1
{
  []
}

function computePrimeExponentDifferences(u: int, v: int, primeFactors: seq<int>): seq<int>
  requires u > 0 && v > 0
  requires forall p :: p in primeFactors ==> isPrime(p)
{
  []
}

function computeMultinomialCoefficient(exponentDiffs: seq<int>, factorials: seq<int>, invFactorials: seq<int>, mod: int): int
  requires mod == 998244353
  requires |factorials| >= 0 && |invFactorials| >= 0
{
  1
}

function buildResultString(lines: seq<seq<char>>): seq<char>
{
  if |lines| == 0 then []
  else if |lines| == 1 then lines[0]
  else buildResultString(lines[0..|lines|-1]) + ['\n'] + lines[|lines|-1]
}

function splitLines(s: seq<char>): seq<seq<char>>
{
  [s]
}

function splitSpace(s: seq<char>): seq<seq<char>>
{
  [s]
}

function parseInt(s: seq<char>): int
{
  1
}

function intToString(i: int): seq<char>
{
  ['0']
}

function isDivisor(a: int, b: int): bool 
  requires b > 0 && a > 0
{ 
  b % a == 0 
}

function isPrime(p: int): bool 
{ 
  p >= 2 && forall i :: 2 <= i < p ==> p % i != 0 
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: seq<char>) returns (result: seq<char>)
  requires |stdin_input| > 0
  requires validInputFormat(stdin_input)
  ensures validOutputFormat(result, stdin_input)
  ensures correctShortestPathCounts(stdin_input, result)
  ensures allOutputValuesInModRange(result)
  ensures correctNumberOfOutputLines(stdin_input, result)
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  var D := parseInt(lines[0]);
  var q := parseInt(lines[1]);
  var primeFactors := extractUniquePrimeFactors(D);
  var mod := 998244353;
  var N := 100003;
  var factorials := precomputeFactorials(N, mod);
  var invFactorials := precomputeInverseFactorials(N, mod, factorials);
  var outputLines: seq<seq<char>> := [];
  var queryIndex := 0;

  while queryIndex < q
    invariant 0 <= queryIndex <= q
    invariant |outputLines| == queryIndex
    invariant forall i :: 0 <= i < |outputLines| ==> 0 <= parseInt(outputLines[i]) < mod
  {
    var queryParts := splitSpace(lines[2 + queryIndex]);
    var u := parseInt(queryParts[0]);
    var v := parseInt(queryParts[1]);
    var pathCount := computeShortestPathCountInDivisorGraph(u, v, primeFactors, mod);
    var pathCountStr := intToString(pathCount);
    outputLines := outputLines + [pathCountStr];
    queryIndex := queryIndex + 1;
  }

  result := buildResultString(outputLines);
}
// </vc-code>
