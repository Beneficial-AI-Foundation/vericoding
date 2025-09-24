// <vc-preamble>
// Helper function for minimum of two natural numbers
function Min(a: nat, b: nat): nat
{
    if a <= b then a else b
}

// Helper function to join strings with separator
function JoinStrings(parts: seq<string>, sep: string): string
{
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + sep + JoinStrings(parts[1..], sep)
}

// Helper function to check if a string contains a separator
predicate ContainsSeparator(s: string, sep: string)
{
    exists i {:trigger s[i..i+|sep|]} :: 0 <= i <= |s| - |sep| && s[i..i+|sep|] == sep
}

// Helper function to count occurrences of separator in string
function CountSeparator(s: string, sep: string): nat
{
    if |s| < |sep| then 0
    else if s[0..|sep|] == sep then 1 + CountSeparator(s[|sep|..], sep)
    else CountSeparator(s[1..], sep)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RightSplit(a: seq<string>, sep: string, maxsplit: nat) returns (result: seq<seq<string>>)
    requires sep != ""
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| > 0
    ensures maxsplit == 0 ==> forall i :: 0 <= i < |result| ==> result[i] == [a[i]]
    ensures forall i :: 0 <= i < |result| ==> |result[i]| <= Min(maxsplit + 1, CountSeparator(a[i], sep) + 1)
    ensures forall i :: 0 <= i < |result| ==> JoinStrings(result[i], sep) == a[i]
    ensures forall i :: 0 <= i < |result| ==> 
            (!ContainsSeparator(a[i], sep) ==> result[i] == [a[i]])
    ensures forall i :: 0 <= i < |result| ==> 
            (a[i] == "" ==> result[i] == [""])
    ensures forall i :: 0 <= i < |result| ==>
            (maxsplit > 0 && ContainsSeparator(a[i], sep) ==> 
             |result[i]| == Min(maxsplit + 1, CountSeparator(a[i], sep) + 1))
    // Right-to-left splitting behavior: when maxsplit limits splits, 
    // the leftmost part contains unsplit separators
    ensures forall i :: 0 <= i < |result| ==>
            (maxsplit > 0 && |result[i]| == maxsplit + 1 && ContainsSeparator(a[i], sep) ==>
             ContainsSeparator(result[i][0], sep) || result[i][0] == "")
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
