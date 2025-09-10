predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists i, j :: 0 <= i < j < |input| && input[i] == ' ' && input[j] == ' ' &&
    (
        var parts := SplitStringSpec(input);
        |parts| >= 3 && 
        IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) &&
        var A := StringToIntSpec(parts[0]);
        var B := StringToIntSpec(parts[1]);
        var C := StringToIntSpec(parts[2]);
        1 <= A <= 100 && 1 <= B <= 100 && 1 <= C <= 100
    )
}

function ComputeDrinks(A: int, B: int, C: int): int
    requires A >= 1 && B >= 1 && C >= 1
{
    if B / A < C then B / A else C
}

function IsValidInteger(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToIntSpec(s: string): int
    requires IsValidInteger(s)
    ensures StringToIntSpec(s) >= 0
{
    if |s| == 1 then s[0] as int - '0' as int
    else StringToIntSpec(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function SplitStringSpec(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitStringSpec(s)| ==> |SplitStringSpec(s)[i]| > 0
    ensures forall i :: 0 <= i < |SplitStringSpec(s)| ==> forall j :: 0 <= j < |SplitStringSpec(s)[i]| ==> SplitStringSpec(s)[i][j] != ' ' && SplitStringSpec(s)[i][j] != '\n' && SplitStringSpec(s)[i][j] != '\t'
{
    if |s| == 0 then []
    else 
        var parts := SplitHelper(s, 0, "");
        parts
}

function SplitHelper(s: string, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    requires forall j :: 0 <= j < |current| ==> current[j] != ' ' && current[j] != '\n' && current[j] != '\t'
    decreases |s| - index
    ensures forall i :: 0 <= i < |SplitHelper(s, index, current)| ==> |SplitHelper(s, index, current)[i]| > 0
    ensures forall i :: 0 <= i < |SplitHelper(s, index, current)| ==> forall j :: 0 <= j < |SplitHelper(s, index, current)[i]| ==> SplitHelper(s, index, current)[i][j] != ' ' && SplitHelper(s, index, current)[i][j] != '\n' && SplitHelper(s, index, current)[i][j] != '\t'
{
    if index >= |s| then
        if |current| > 0 then [current] else []
    else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' then
        if |current| > 0 then [current] + SplitHelper(s, index + 1, "")
        else SplitHelper(s, index + 1, "")
    else
        SplitHelper(s, index + 1, current + [s[index]])
}

function IntToStringSpec(n: int): string
    requires n >= 0
    ensures |IntToStringSpec(n)| > 0
    ensures forall i :: 0 <= i < |IntToStringSpec(n)| ==> '0' <= IntToStringSpec(n)[i] <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToStringSpec(n / 10) + [('0' as int + (n % 10)) as char]
}

// <vc-helpers>
function StringToChar(s: string, i: int): char
  requires 0 <= i < |s|
{
  s[i]
}

function StringToDigits(s: string): (digits: seq<int>)
  requires IsValidInteger(s)
  ensures |digits| == |s|
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  if |s| == 0 then []
  else [StringToChar(s, 0) as int - '0' as int] + StringToDigits(s[1..])
}

lemma StringToIntLemma(s: string)
  requires IsValidInteger(s)
  ensures StringToIntSpec(s) == (
    if |s| == 0 then 0
    else var value := 0;
         for i := 0 to |s|-1 {
           value := value * 10 + (s[i] as int - '0' as int);
         }
         value
  )
{
  if |s| == 0 {
    // StringToIntSpec(s) returns 0 for empty string if extended, but the spec
    // assumes |s| > 0, so this case is only theoretical for the loop.
    // However, for the recursive function, StringToIntSpec("") is not defined by requires.
    // The current spec has requires IsValidInteger(s), which implies |s| > 0.
  } else {
    var value := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant value == (
        var current_val := 0;
        for k := 0 to i-1 {
          current_val := current_val * 10 + (s[k] as int - '0' as int);
        }
        current_val
      )
    {
      value := value * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
  }
}

ghost method ComputeInt(s: string) returns (value: int)
  requires IsValidInteger(s)
  ensures value == StringToIntSpec(s)
{
  value := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant value == StringToIntSpec(s[..i])
  {
    value := value * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
}

lemma IntToStringLemma(n: int)
  requires n >= 0
  ensures IntToStringSpec(n) == (
    if n == 0 then "0"
    else var s := "";
         var temp_n := n;
         while temp_n > 0
           invariant temp_n >= 0
           invariant s == (
             var res := "";
             var t_n := temp_n;
             var pow10 := 1;
             while t_n / pow10 > 0 { pow10 := pow10 * 10; }
             pow10 := pow10 / 10;
             while pow10 > 0 {
               res := res + [('0' as int + (t_n / pow10) % 10) as char];
               pow10 := pow10 / 10;
             }
             if temp_n == 0 then "0" else res
           ).reversed()
             // A more exact invariant for reverse accumulation would be:
             // Let D = sequence of digits of n. Let S = sequence of digits of temp_n.
             // s == D[|D|-|S| ..].Reverse()
             // It essentially proves that s contains the digits of (n mod 10^k) in reverse order.
             invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
         {
           s := [('0' as int + (temp_n % 10)) as char] + s;
           temp_n := temp_n / 10;
         }
         s
  )
{
  if n == 0 {
  } else {
    var res_s := "";
    var temp_n := n;
    while temp_n > 0
      invariant temp_n >= 0
      invariant forall k :: 0 <= k < |res_s| ==> '0' <= res_s[k] <= '9'
      invariant res_s == ReverseString(IntToStringSpec(n)[|IntToStringSpec(temp_n).().| ..]);
    {
      res_s := [('0' as int + (temp_n % 10)) as char] + res_s;
      temp_n := temp_n / 10;
    }
  }
}

function Power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

function ReverseString(s: string): string
{
  if |s| == 0 then ""
  else ReverseString(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures (
        var parts := SplitStringSpec(input);
        var A := StringToIntSpec(parts[0]);
        var B := StringToIntSpec(parts[1]);
        var C := StringToIntSpec(parts[2]);
        var drinks := ComputeDrinks(A, B, C);
        result == IntToStringSpec(drinks) + "\n"
    )
// </vc-spec>
// <vc-code>
{
    var parts := SplitStringSpec(input);
    var partA := parts[0];
    var partB := parts[1];
    var partC := parts[2];

    var A: int;
    A := 0;
    var i := 0;
    while i < |partA|
        invariant 0 <= i <= |partA|
        invariant A == StringToIntSpec(partA[..i])
        // Need to add invariant relating A to StringToIntSpec(partA)
        // This is tricky, a ghost method could help here for sure
    {
        A := A * 10 + (partA[i] as int - '0' as int);
        i := i + 1;
    }
    // After the loop, A should be equal to StringToIntSpec(partA)
    // The spec proves this for StringToIntSpec(s) used in the code
    // We can use StringToIntSpec(partA) directly.

    var B: int;
    B := 0;
    i := 0; // Reset i
    while i < |partB|
        invariant 0 <= i <= |partB|
        invariant B == StringToIntSpec(partB[..i])
    {
        B := B * 10 + (partB[i] as int - '0' as int);
        i := i + 1;
    }

    var C: int;
    C := 0;
    i := 0; // Reset i
    while i < |partC|
        invariant 0 <= i <= |partC|
        invariant C == StringToIntSpec(partC[..i])
    {
        C := C * 10 + (partC[i] as int - '0' as int);
        i := i + 1;
    }

    var drinks := ComputeDrinks(A, B, C);

    var res_s := "";
    if drinks == 0 {
        res_s := "0";
    } else {
        var temp_n := drinks;
        while temp_n > 0
            invariant temp_n >= 0
            invariant forall k :: 0 <= k < |res_s| ==> '0' <= res_s[k] <= '9'
            invariant res_s == ReverseString(IntToStringSpec(drinks)[|IntToStringSpec(temp_n).().| ..]);
        {
            res_s := [('0' as int + (temp_n % 10)) as char] + res_s;
            temp_n := temp_n / 10;
        }
    }
    result := res_s + "\n";
}
// </vc-code>

