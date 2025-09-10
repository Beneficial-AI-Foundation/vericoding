predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists i :: 0 <= i < |input| && input[i] == ' ') &&
    (forall j :: 0 <= j < |input| ==> ('0' <= input[j] <= '9' || input[j] == ' ' || input[j] == '\n'))
}

function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) > 0 || (a == 0 && b == 0)
    ensures a > 0 ==> gcd(a, b) <= a
    ensures b > 0 ==> gcd(a, b) <= b
    ensures (a != 0 || b != 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
    ensures gcd(a, 0) == a
    ensures gcd(0, b) == b
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a  
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function f_mathematical(x: nat, y: nat): nat
    ensures y == 0 ==> f_mathematical(x, y) == 0
    ensures y > 0 ==> f_mathematical(x, y) > 0
    ensures y > 0 ==> f_mathematical(x, y) <= y
    ensures y > 0 ==> f_mathematical(x, y) == 1 + f_mathematical(x, y - gcd(x, y))
    decreases y
{
    if y == 0 then 0
    else 
        var g := gcd(x, y);
        if g >= y then 1
        else 1 + f_mathematical(x, y - g)
}

predicate ValidOutput(result: string)
{
    |result| > 0 &&
    forall i :: 0 <= i < |result| ==> ('0' <= result[i] <= '9' || result[i] == '\n') &&
    result[|result|-1] == '\n'
}

// <vc-helpers>
predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists i :: 0 <= i < |input| && input[i] == ' ') &&
    forall j :: 0 <= j < |input| ==> ('0' <= input[j] <= '9' || input[j] == ' ' || input[j] == '\n')
}

function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) > 0 || (a == 0 && b == 0)
    ensures a > 0 ==> gcd(a, b) <= a
    ensures b > 0 ==> gcd(a, b) <= b
    ensures (a != 0 || b != 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
    ensures gcd(a, 0) == a
    ensures gcd(0, b) == b
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a  
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function f_mathematical(x: nat, y: nat): nat
    ensures y == 0 ==> f_mathematical(x, y) == 0
    ensures y > 0 ==> f_mathematical(x, y) > 0
    ensures y > 0 ==> f_mathematical(x, y) <= y
    ensures y > 0 ==> f_mathematical(x, y) == 1 + f_mathematical(x, y - gcd(x, y))
    decreases y
{
    if y == 0 then 0
    else 
        var g := gcd(x, y);
        if g >= y then 1
        else 1 + f_mathematical(x, y - g)
}

predicate ValidOutput(result: string)
{
    |result| > 0 &&
    forall i :: 0 <= i < |result| ==> ('0' <= result[i] <= '9' || result[i] == '\n') &&
    result[|result|-1] == '\n'
}

function atoi(s: seq<char>): nat
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures atoi(s) >= 0
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else 10 * atoi(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function itoa(n: nat): seq<char>
  ensures |itoa(n)| > 0
  ensures forall i :: 0 <= i < |itoa(n)| ==> '0' <= itoa(n)[i] <= '9'
  ensures atoi(itoa(n)) == n
  decreases n
{
  if n == 0 then ['0']
  else itoa(n / 10) + [((n % 10 + ('0' as int)) as char)]
}

method get_tokens(input: seq<char>) returns (tokens: seq<seq<char>>)
  requires ValidInput(input)
  ensures forall t :: t in tokens ==> |t| > 0 && forall i :: 0 <= i < |t| ==> '0' <= t[i] <= '9'
  ensures |tokens| > 0  // Since at least one space, and |input| > 0, must have tokens
{
  tokens := [];
  var i := 0;
  while i < |input|
    invariant forall t :: t in tokens ==> |t| > 0 && forall i :: 0 <= i < |t| ==> '0' <= t[i] <= '9'
  {
    if '0' <= input[i] <= '9' {
      var j := i + 1;
      while j < |input| && '0' <= input[j] <= '9' {
        j := j + 1;
      }
      tokens := tokens + [input[i..j]];
      i := j;
    } else if input[i] == ' ' || input[i] == '\n' {
      i := i + 1;
    } else {
      // ValidInput ensures only digits, space, \n, so skipping non-digit
      i := i + 1;
    }
  }
}

method get_pairs(input: seq<char>) returns (pairs: seq<(nat, nat)>)
  requires ValidInput(input)
{
  var tokens := get_tokens(input);
  pairs := [];
  var i := 0;
  while i + 1 < |tokens|
    invariant i % 2 == 0 ==> |pairs| == i / 2
  {
    var a := atoi(tokens[i]);
    var b := atoi(tokens[i+1]);
    pairs := pairs + [(a, b)];
    i := i + 2;
  }
  // If odd number of tokens, last one ignored
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var pairs := get_pairs(input);
  result := "";
  var k := 0;
  while k < |pairs|
  {
    var (a, b) := pairs[k];
    var f_val := f_mathematical(a, b);
    var s := itoa(f_val) + ['\n'];
    result := result + s;
    k := k + 1;
  }
}
// </vc-code>

