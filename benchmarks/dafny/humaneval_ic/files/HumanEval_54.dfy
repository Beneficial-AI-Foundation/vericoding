This task involves determining if two strings contain exactly the same set of unique characters, regardless of character frequency or order. The implementation should compare the set of characters in each string and return true if they are identical sets.

// ======= TASK =======
// Given two strings, determine if they contain exactly the same set of unique characters, 
// regardless of character frequency or order.

// ======= SPEC REQUIREMENTS =======
function CharSet(s: string): set<char>
{
    set c | c in s
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method same_chars(s0: string, s1: string) returns (result: bool)
    ensures result == (CharSet(s0) == CharSet(s1))
{
    var set0 := set c | c in s0;
    var set1 := set c | c in s1;
    result := set0 == set1;
}
