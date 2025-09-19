// <vc-preamble>
// Helper predicate to check if a character is lowercase
predicate IsLowerCase(c: char)
{
    'a' <= c <= 'z'
}

// Helper predicate to check if a character is uppercase  
predicate IsUpperCase(c: char)
{
    'A' <= c <= 'Z'
}

// Helper predicate to check if a character is alphabetic
predicate IsAlphabetic(c: char)
{
    IsLowerCase(c) || IsUpperCase(c)
}

// Helper function to convert character to uppercase
function ToUpperCase(c: char): char
    requires IsLowerCase(c)
{
    (c as int - 'a' as int + 'A' as int) as char
}

// Helper function to convert character to lowercase
function ToLowerCase(c: char): char
    requires IsUpperCase(c)
{
    (c as int - 'A' as int + 'a' as int) as char
}

// Helper function to swap case of a single character
function SwapCaseChar(c: char): char
{
    if IsLowerCase(c) then ToUpperCase(c)
    else if IsUpperCase(c) then ToLowerCase(c)  
    else c
}

// Helper function to swap case of a single string
function SwapCaseString(s: string): string
{
    seq(|s|, i requires 0 <= i < |s| => SwapCaseChar(s[i]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method swapcase(a: seq<string>) returns (result: seq<string>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> 
        // Length preservation for each string
        |result[i]| == |a[i]| &&
        // Empty string handling
        (|a[i]| == 0 ==> result[i] == "") &&
        // Character-level transformation correctness
        (forall j :: 0 <= j < |a[i]| ==> 
            result[i][j] == SwapCaseChar(a[i][j])) &&
        // Case transformation specifics
        (forall j :: 0 <= j < |a[i]| ==> 
            (IsLowerCase(a[i][j]) ==> result[i][j] == ToUpperCase(a[i][j])) &&
            (IsUpperCase(a[i][j]) ==> result[i][j] == ToLowerCase(a[i][j])) &&
            (!IsAlphabetic(a[i][j]) ==> result[i][j] == a[i][j])) &&
        // Involutive property: swapping case twice yields original
        (forall j :: 0 <= j < |a[i]| ==> 
            SwapCaseChar(SwapCaseChar(a[i][j])) == a[i][j]) &&
        // Result is exactly the case-swapped version of original
        result[i] == SwapCaseString(a[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
