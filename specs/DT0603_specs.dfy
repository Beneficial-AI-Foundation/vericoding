// <vc-preamble>
/*
 * This file implements string capitalization functionality for arrays of strings.
 * It provides a method to capitalize the first character of each string element
 * while preserving the length and structure of the input array.
 */

// Helper function to check if a character is a lowercase letter
predicate IsLowercase(c: char)
{
    'a' <= c <= 'z'
}

// Helper function to check if a character is an uppercase letter  
predicate IsUppercase(c: char)
{
    'A' <= c <= 'Z'
}

// Helper function to convert lowercase to uppercase
function ToUppercase(c: char): char
    requires IsLowercase(c)
{
    (c as int - 'a' as int + 'A' as int) as char
}

// Helper function to convert uppercase to lowercase
function ToLowercase(c: char): char
    requires IsUppercase(c)
{
    (c as int - 'A' as int + 'a' as int) as char
}

// Helper function to capitalize a single character
function CapitalizeChar(c: char): char
{
    if IsLowercase(c) then ToUppercase(c) else c
}

// Helper function to make a character lowercase
function LowercaseChar(c: char): char
{
    if IsUppercase(c) then ToLowercase(c) else c
}

// Helper function to capitalize a single string
function CapitalizeString(s: string): string
{
    if |s| == 0 then ""
    else [CapitalizeChar(s[0])] + seq(|s| - 1, i => LowercaseChar(s[i + 1]))
}

// Main method that capitalizes each string in the input array
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Capitalize(a: array<string>) returns (result: array<string>)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
