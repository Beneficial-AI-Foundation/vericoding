// <vc-preamble>
// Helper predicate to check if a character is uppercase
predicate IsUpperCase(c: char)
{
    'A' <= c <= 'Z'
}

// Helper predicate to check if a character is lowercase  
predicate IsLowerCase(c: char)
{
    'a' <= c <= 'z'
}

// Helper predicate to check if a character is alphabetic
predicate IsAlphabetic(c: char)
{
    IsUpperCase(c) || IsLowerCase(c)
}

// Helper function to convert a single character to lowercase
function ToLowerChar(c: char): char
{
    if IsUpperCase(c) then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}

// Helper function to convert a string to lowercase
function ToLowerString(s: string): string
{
    seq(|s|, i requires 0 <= i < |s| => ToLowerChar(s[i]))
}

// Helper predicate to check if a string is already in lowercase
predicate IsLowerCaseString(s: string)
{
    forall i :: 0 <= i < |s| ==> !IsUpperCase(s[i])
}

/**
 * Converts each string element in the input sequence to lowercase.
 * Preserves sequence length and individual string lengths while applying
 * case transformation to alphabetic characters only.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Lower(a: seq<string>) returns (result: seq<string>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == ToLowerString(a[i])
    ensures forall i :: 0 <= i < |a| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |a| ==> a[i] == "" ==> result[i] == ""
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            result[i][j] == ToLowerChar(a[i][j])
    ensures forall i :: 0 <= i < |a| ==> IsLowerCaseString(result[i])
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            !IsAlphabetic(a[i][j]) ==> result[i][j] == a[i][j]
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            IsUpperCase(a[i][j]) ==> IsLowerCase(result[i][j])
    ensures forall i :: 0 <= i < |result| ==> ToLowerString(result[i]) == result[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
