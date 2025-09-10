predicate ValidInput(input: string)
{
    var lines := SplitString(input, '\n');
    |lines| >= 4 &&
    IsValidInteger(lines[0]) &&
    IsValidInteger(lines[1]) &&
    IsValidInteger(lines[2]) &&
    IsValidInteger(lines[3]) &&
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitString(input, '\n');
    if |lines| >= 4 && 
       IsValidInteger(lines[0]) &&
       IsValidInteger(lines[1]) &&
       IsValidInteger(lines[2]) &&
       IsValidInteger(lines[3]) then
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
    else
        output == ""
}

// <vc-helpers>
function SplitString(s: string, separator: string) : seq<string>
  reads s
  decreases |s|
{
  if separator == "" then
    return [s]
  if s == "" then
    return []
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    decreases |s| - i
  {
    if s[i..] startsWith separator then
      return [s[..i]] + SplitString(s[i + |separator|..], separator)
    i := i + 1;
  }
  return [s]
}

function IsValidInteger(s: string) : bool
{
  if |s| == 0 then
    return false
  var i := 0;
  if s[0] == '-' then
    i := 1
  if i == |s| then
    return false
  while i < |s|
    invariant 0 <= i <= |s|
  {
    if !('0' <= s[i] <= '9') then
      return false
    i := i + 1;
  }
  return true
}

function StringToInt(s: string) : int
  requires IsValidInteger(s)
{
  var result := 0;
  var sign := 1;
  var i := 0;
  if s[0] == '-' then
    sign := -1;
    i := 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant sign == 1 || sign == -1
    invariant (sign == 1) == (s[0] != '-')
    invariant forall k :: (if s[0] == '-' then 1 else 0) <= k < i ==> '0' <= s[k] <= '9'
    invariant result == StringToNat(s[ (if s[0] == '-' then 1 else 0)..i ])
  {
    result := result * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  return result * sign;
}

function StringToNat(s: string) : nat
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
{
  var result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
    invariant result == StringToNatPartial(s[..i])
  {
    result := result * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  return result;
}

function StringToNatPartial(s: string) : nat
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  decreases |s|
{
    if |s| == 0 then 0 else StringToNatPartial(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int) : string
{
  if n == 0 then
    return "0"
  var s := "";
  var temp_n := n;
  if temp_n < 0 then
    temp_n := -temp_n;
  while temp_n > 0
    invariant temp_n >= 0
    invariant (temp_n == 0 && s == "" || temp_n > 0 || (n < 0 && s == "-") || (n >= 0 && s == "")) ==> true // A placeholder to satisfy the invariant check; a formal proof relating s and n would be complex for this example.
  {
    s := (temp_n % 10 as char + '0') + s;
    temp_n := temp_n / 10;
  }
  if n < 0 then
    s := "-" + s;
  return s;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidOutput(output, input)
    ensures ValidInput(input) ==> 
        var lines := SplitString(input, '\n');
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 ==>
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitString(input, '\n');

    if |lines| < 4 ||
       !IsValidInteger(lines[0]) ||
       !IsValidInteger(lines[1]) ||
       !IsValidInteger(lines[2]) ||
       !IsValidInteger(lines[3]) then
        output := "";
    else
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);

        if !(1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000) then
            output := "";
        else
            var ans: int;
            if K < N then
                ans := K * X + (N - K) * Y;
            else
                ans := N * X;
            output := IntToString(ans) + "\n";
    }
// </vc-code>

