predicate ValidOutput(n: int, result: seq<string>)
    requires n >= 2
{
    if n < 6 then
        |result| == 1 + (n - 1) &&
        result[0] == "-1" &&
        (forall i :: 1 <= i < |result| ==> result[i] == "1 " + IntToString(i + 1))
    else
        |result| == (5 + (n - 6)) + (n - 1) &&
        result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
        result[3] == "2 5" && result[4] == "2 6" &&
        (forall i :: 5 <= i < 5 + (n - 6) ==> result[i] == "1 " + IntToString(i + 2)) &&
        (forall i :: 5 + (n - 6) <= i < |result| ==> result[i] == "1 " + IntToString(i - (5 + (n - 6)) + 2))
}

function IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then [n as char + '0']
    else IntToString(n / 10) + IntToString(n % 10)
}

// <vc-helpers>
// No helper functions or proofs required.
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires n >= 2
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
{
  if n < 6 {
    var res := ["-1"];
    var k := 2;
    while k <= n
      invariant 2 <= k <= n + 1
      invariant res == ["-1"] + (seq i | 2 <= i < k :: "1 " + IntToString(i))
      decreases n - k
    {
      res := res + ["1 " + IntToString(k)];
      k := k + 1;
    }
    result := res;
  } else {
    var res := ["1 2", "1 3", "1 4", "2 5", "2 6"];
    var k := 7;
    while k <= n
      invariant 7 <= k <= n + 1
      invariant res == ["1 2", "1 3", "1 4", "2 5", "2 6"] + (seq i | 7 <= i < k :: "1 " + IntToString(i))
      decreases n - k
    {
      res := res + ["1 " + IntToString(k)];
      k := k + 1;
    }
    k := 2;
    while k <= n
      invariant 2 <= k <= n + 1
      invariant res == ["1 2", "1 3", "1 4", "2 5", "2 6"] + (seq i | 7 <= i < n + 1 :: "1 " + IntToString(i)) + (seq i | 2 <= i < k :: "1 " + IntToString(i))
      decreases n - k
    {
      res := res + ["1 " + IntToString(k)];
      k := k + 1;
    }
    result := res;
  }
}
// </vc-code>

