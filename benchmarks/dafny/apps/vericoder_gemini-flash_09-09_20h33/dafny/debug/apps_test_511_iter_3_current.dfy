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
function parseNat(s: string): nat
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  returns (n: nat)
  ensures s == "0" ==> n == 0
  ensures s != "0" ==> n > 0
  ensures |s| > 0 ==> n == (s[0] - '0') * (if |s| > 1 then power(10, |s|-1) else 1) + (if |s| > 1 then parseNat(s[1..]) else 0)
  decreases |s|
{
  if |s| == 0 then 0
  else if |s| == 1 then (s[0] - '0')
  else (s[0] - '0') * power(10, |s|-1) + parseNat(s[1..])
}

function power(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

lemma lemma_parseNat(s: string)
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures |s| > 0 ==> parseNat(s) >= 0
  ensures |s| == 1 ==> parseNat(s) == (s[0] - '0')
  ensures |s| > 1 ==> parseNat(s) == (s[0] - '0') * power(10, |s|-1) + parseNat(s[1..])
{}

lemma lemma_chars_are_digits(s: string)
    ensures (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') ==> (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}

predicate IsDigit(c: char) { '0' <= c <= '9' }

lemma lemma_digits_to_string(n: nat)
  ensures forall i :: 0 <= i < |n.ToString()| ==> IsDigit(n.ToString()[i])
{}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var lines_arr := new array<string>(0);
    var currentLineStart := 0;
    for i := 0 to |input|
        invariant 0 <= i <= |input|
        invariant currentLineStart <= i
        invariant (forall j :: 0 <= j < lines_arr.Length ==> (exists k, l :: 0 <= k <= l <= |input| && lines_arr[j] == input[k..l]))
        invariant currentLineStart == i || (i > 0 && input[i-1] == '\n') || i == 0
    {
        if i == |input| || input[i] == '\n' {
            var line := input[currentLineStart .. i];
            lines_arr := lines_arr + [line];
            currentLineStart := i + 1;
        }
    }

    var results := new array<nat>(0);
    for line_idx := 0 to lines_arr.Length
        invariant 0 <= line_idx <= lines_arr.Length
        invariant forall j :: 0 <= j < results.Length ==> exists x, y :: x >=0 && y >=0 && results[j] == f_mathematical(x, y)
    {
        if line_idx == lines_arr.Length then break;
        var line := lines_arr[line_idx];
        var space_idx := -1;
        for i := 0 to |line|
            invariant 0 <= i <= |line|
        {
            if i < |line| && line[i] == ' ' {
                space_idx := i;
                break;
            }
        }

        if space_idx != -1 {
            var x_str := line[0 .. space_idx];
            var y_str := line[space_idx + 1 ..];
            
            // Prove that x_str and y_str only contain digits
            lemma_chars_are_digits(x_str);
            lemma_chars_are_digits(y_str);

            var x := parseNat(x_str);
            var y := parseNat(y_str);
            
            var fx := f_mathematical(x, y);
            results := results + [fx];
        }
    }
    
    var res_str := "";
    for i := 0 to results.Length
      invariant 0 <= i <= results.Length
      invariant forall j :: 0 <= j < |res_str| ==> ('0' <= res_str[j] <= '9' || res_str[j] == '\n')
    {
      if i < results.Length {
        lemma_digits_to_string(results[i]);
        res_str := res_str + results[i].ToString() + "\n";
      }
    }
    return res_str;
}
// </vc-code>

