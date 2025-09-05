Implement a function that returns the length of a given string. The function should handle empty strings and return 0 for them. For non-empty strings, it should return the count of characters.

// ======= TASK =======
// Implement a function that returns the length of a given string.
// The function should handle empty strings and return 0 for them.
// For non-empty strings, it should return the count of characters.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(s: string)
{
    true
}

function CorrectLength(s: string): int
{
    |s|
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
function strlen(s: string): int
    requires ValidInput(s)
    ensures strlen(s) >= 0
    ensures strlen(s) == CorrectLength(s)
{
    |s|
}
