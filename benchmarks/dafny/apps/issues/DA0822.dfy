// <vc-preamble>
predicate ValidInput(n: int, k: int) {
  1 <= n <= 150 && 0 <= k <= 9
}

function DigitSum(x: int): int
  requires x >= 0
  ensures DigitSum(x) >= 0
  ensures x == 0 ==> DigitSum(x) == 0
  ensures x > 0 ==> DigitSum(x) == (x % 10) + DigitSum(x / 10)
{
  if x == 0 then 0
  else (x % 10) + DigitSum(x / 10)
}

function SumDigitSums(x: int, k: int): int
  requires x >= 0 && k >= 0
  ensures SumDigitSums(x, k) >= 0
  ensures k == 0 ==> SumDigitSums(x, k) == DigitSum(x)
  ensures k > 0 ==> SumDigitSums(x, k) == DigitSum(x) + SumDigitSums(x + 1, k - 1)
  decreases k
{
  if k == 0 then DigitSum(x)
  else DigitSum(x) + SumDigitSums(x + 1, k - 1)
}

predicate CorrectResult(result: int, n: int, k: int) 
  requires ValidInput(n, k)
{
  result == -1 || (result >= 0 && SumDigitSums(result, k) == n)
}
// </vc-preamble>

// <vc-helpers>
function StringToInt(s: string): int
  ensures StringToInt(s) >= 0
{
  if |s| == 0 then 0
  else if |s| == 1 then 
    if s[0] == '0' then 0
    else if s[0] == '1' then 1
    else if s[0] == '2' then 2
    else if s[0] == '3' then 3
    else if s[0] == '4' then 4
    else if s[0] == '5' then 5
    else if s[0] == '6' then 6
    else if s[0] == '7' then 7
    else if s[0] == '8' then 8
    else if s[0] == '9' then 9
    else 0
  else
    StringToInt(s[..|s|-1]) * 10 + StringToInt(s[|s|-1..])
}

function IntToString(x: int): string
  requires x >= 0
  ensures |IntToString(x)| >= 1
  ensures x == 0 ==> IntToString(x) == "0"
{
  if x == 0 then "0"
  else if x < 10 then
    if x == 1 then "1"
    else if x == 2 then "2"
    else if x == 3 then "3"
    else if x == 4 then "4"
    else if x == 5 then "5"
    else if x == 6 then "6"
    else if x == 7 then "7"
    else if x == 8 then "8"
    else "9"
  else
    IntToString(x / 10) + IntToString(x % 10)
}

function RepeatString(s: string, count: int): string
  requires count >= 0
  ensures |RepeatString(s, count)| == count * |s|
  ensures count == 0 ==> RepeatString(s, count) == ""
{
  if count == 0 then ""
  else s + RepeatString(s, count - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int)>) returns (results: seq<int>)
  requires forall i :: 0 <= i < |testCases| ==> ValidInput(testCases[i].0, testCases[i].1)
  ensures |results| == |testCases|
  ensures forall i :: 0 <= i < |results| ==> CorrectResult(results[i], testCases[i].0, testCases[i].1)
// </vc-spec>
// <vc-code>
{
  results := [];
  var INF := 1000000000;

  for test := 0 to |testCases|
    invariant |results| == test
    invariant forall i :: 0 <= i < |results| ==> CorrectResult(results[i], testCases[i].0, testCases[i].1)
  {
    var n := testCases[test].0;
    var k := testCases[test].1;
    var res := INF;

    for numK := 0 to 17
      invariant res == INF || (res >= 0 && SumDigitSums(res, k) == n)
    {
      for d := 0 to 10
        invariant res == INF || (res >= 0 && SumDigitSums(res, k) == n)
      {
        var tmp := 0;
        for i := 0 to k + 1
        {
          if d + i <= 9 {
            tmp := tmp + 9 * numK + d + i;
          } else {
            tmp := tmp + 1 + (d + i) - 10;
          }
        }

        if n >= tmp && (n - tmp) % (k + 1) == 0 {
          var s := (n - tmp) / (k + 1);
          var prefix: string;

          if s <= 8 {
            prefix := IntToString(s);
          } else {
            var quotient := (s - 8) / 9;
            var remainder := (s - 8) % 9;
            var tmpCall1 := IntToString(remainder);
            var tmpCall2 := RepeatString("9", quotient);
            prefix := tmpCall1 + tmpCall2 + "8";
          }

          var tmpCall3 := RepeatString("9", numK);
          var tmpCall4 := IntToString(d);
          prefix := prefix + tmpCall3 + tmpCall4;
          var x := StringToInt(prefix);

          if SumDigitSums(x, k) == n {
            if x < res {
              res := x;
            }
          }
        }
      }
    }

    if res == INF {
      results := results + [-1];
    } else {
      assert res >= 0 && SumDigitSums(res, k) == n;
      results := results + [res];
    }
  }
}
// </vc-code>
