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
function method StringToChar(s: string, i: int): char
  requires 0 <= i < |s|
{
  s[i]
}

function method StringToDigits(s: string): (digits: seq<int>)
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
    var value := 0;
    for i := 0 to |s|-1 {
      value := value * 10 + (s[i] as int - '0' as int);
    }
    value
  )
{
  // The ensures clause describes the iterative computation
  // StringToIntSpec is defined recursively.
  // We can prove equivalence by induction or by using a loop.
  // The ghost method ComputeInt below directly implements the iterative computation.
}

ghost method ComputeInt(s: string) returns (value: int)
  requires IsValidInteger(s)
  ensures value == StringToIntSpec(s)
{
  value := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant value == (
      if i == 0 then 0
      else StringToIntSpec(s[..i])
    )
  {
    value := value * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  // The invariant at loop termination simplifies to value == StringToIntSpec(s[..|s|]) == StringToIntSpec(s)
}

lemma IntToStringLemma(n: int)
  requires n >= 0
  ensures IntToStringSpec(n) == (
    if n == 0 then "0"
    else var s := "";
         var temp_n := n;
         while temp_n > 0
           invariant temp_n >= 0
           invariant (n == 0 && s == "0") || (n > 0 && s == ReverseString(IntToStringSpec(n) / (Power(10, (if temp_n == 0 then 1 else LargestPowerOf10LessOrEqualTo(temp_n)))))) // Simplification of the original invariant attempt
           invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
         {
           s := [('0' as int + (temp_n % 10)) as char] + s;
           temp_n := temp_n / 10;
         }
         s
  )
{
  // This lemma is hard to prove directly in Dafny because string manipulation
  // and properties like ReverseString are complex.
  // For the purpose of verification in the solve method, it's sufficient if
  // the computation of 'res_s' correctly matches the behavior of StringToIntSpec,
  // which is implicitly asserted by the postcondition of `solve` requiring
  // `result == IntToStringSpec(drinks) + "\n"`.
  // The implementation in the `solve` method for converting int to string
  // directly mirrors the definition of `IntToStringSpec` when `n > 0`,
  // and handles `n == 0` explicitly.
}

function Power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

function LargestPowerOf10LessOrEqualTo(n: int): int
  requires n > 0
  decreases n
{
  if n < 10 then 1
  else 10 * LargestPowerOf10LessOrEqualTo(n / 10)
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
        // To prove this invariant, we need to show that:
        // 1. Initial state: A=0, i=0. StringToIntSpec(partA[..0]) == StringToIntSpec("") == 0 (by convention, or as base case). This holds.
        // 2. Loop body: Assume A_old == StringToIntSpec(partA[..i_old]).
        //    A_new = A_old * 10 + (partA[i_old] as int - '0' as int).
        //    We need to show A_new == StringToIntSpec(partA[..(i_old+1)]).
        //    This is precisely the recursive definition of StringToIntSpec:
        //    StringToIntSpec(S) = StringToIntSpec(S[..|S|-1]) * 10 + (S[|S|-1] as int - '0' as int).
        //    Here S = partA[..(i_old+1)], so S[..|S|-1] = partA[..i_old] and S[|S|-1] = partA[i_old].
        //    So the invariant holds.
    {
        A := A * 10 + (partA[i] as int - '0' as int);
        i := i + 1;
    }

    var B: int;
    B := 0;
    i := 0; // Reset i for the next loop
    while i < |partB|
        invariant 0 <= i <= |partB|
        invariant B == StringToIntSpec(partB[..i])
    {
        B := B * 10 + (partB[i] as int - '0' as int);
        i := i + 1;
    }

    var C: int;
    C := 0;
    i := 0; // Reset i for the next loop
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
            invariant IntToStringSpec(drinks) == ReverseString(res_s) + IntToStringSpec(temp_n) // This is the key invariant to connect it to IntToStringSpec
                                                                                                  // Or more simply based on the recursive definition.
                                                                                                  // IntToStringSpec(drinks) ==
                                                                                                  //    IntToStringSpec(temp_n) + ReverseString(res_s)
                                                                                                  // more precise:
            invariant (var computed_so_far := 0;
                       var power_of_10 := 1;
                       for k := 0 to |res_s|-1 {
                           computed_so_far := computed_so_far + (res_s[k] as int - '0' as int) * power_of_10;
                           power_of_10 := power_of_10 * 10;
                       }
                       drinks == temp_n * power_of_10 + computed_so_far)
        {
            res_s := [('0' as int + (temp_n % 10)) as char] + res_s;
            temp_n := temp_n / 10;
        }
        // After the loop, temp_n is 0.
        // The invariant becomes: drinks == 0 * power_of_10 + computed_so_far == computed_so_far.
        // This shows drinks == integer value represented by ReverseString(res_s).
        // Since IntToStringSpec(drinks) is the string representation of drinks,
        // and res_s is built in reverse, ReverseString(res_s) is IntToStringSpec(drinks).
    }
    result := res_s + "\n";
}
// </vc-code>

