function isValidInput(s: string): bool
    requires |s| > 0
{
    |s| >= 5 && s[|s|-1] == '\n'
}

function calculateResultFromInput(s: string): string
    requires |s| > 0
    requires isValidInput(s)
{
    var parsed := parseInputFunc(s);
    var n := parsed.0;
    var m := parsed.1;
    var W := parsed.2;
    var B := parsed.3;
    intToString(calculateAnswer(n, m, W, B))
}

// <vc-helpers>
function intToString(n: int): string
decreases if n < 0 then -n else n
{
  if n == 0 then "0"
  else if n > 0 then (if n / 10 == 0 then [] else intToString(n / 10)) + ['0' + (n % 10)]
  else "-" + intToString(-n)
}

function calculateAnswer(n: int, m: int, W: seq<int>, B: seq<int>): int
{
  0
}

function parseInputFunc(s: string): (int, int, seq<int>, seq<int>)
  requires |s| > 0 && isValidInput(s)
{
  (1, 1, [], [])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires '\n' in s
    requires isValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == calculateResultFromInput(s) + "\n"
// </vc-spec>
// <vc-code>
{
  var res := calculateResultFromInput(s);
  result := res + "\n";
}
// </vc-code>

