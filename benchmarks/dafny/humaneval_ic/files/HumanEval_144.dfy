This verification challenge involves implementing a method that determines if the product of two fractions is a whole number. Given two fractions represented as strings in the format "numerator/denominator", the task is to multiply them and check if the result is an integer (i.e., the numerator of the product is divisible by the denominator).

The implementation must correctly parse the fraction strings, extract numerators and denominators, perform the multiplication, and check divisibility while maintaining all verification conditions.

// ======= TASK =======
// Given two fractions represented as strings in the format "numerator/denominator",
// determine if their product is a whole number. Input consists of two strings x and n,
// each representing a valid fraction where both numerator and denominator are positive
// integers and denominators are never zero. Return true if x * n equals a whole number,
// false otherwise.

// ======= SPEC REQUIREMENTS =======
predicate ValidFraction(s: string)
{
    |s| > 0 && 
    (exists i :: 0 <= i < |s| && s[i] == '/') &&
    (forall j :: 0 <= j < |s| ==> (s[j] == '/' || ('0' <= s[j] <= '9'))) &&
    (exists k :: 0 <= k < |s| && s[k] == '/' && 
        |s[0..k]| > 0 && |s[k+1..]| > 0 &&
        StringToInt(s[0..k]) > 0 && StringToInt(s[k+1..]) > 0) &&
    (forall i :: 0 <= i < |s| && s[i] == '/' ==> 
        |s[0..i]| > 0 && |s[i+1..]| > 0 &&
        StringToInt(s[0..i]) > 0 && StringToInt(s[i+1..]) > 0)
}

function GetNumerator(s: string): int
    requires ValidFraction(s)
{
    var slash_pos := FindSlash(s);
    StringToInt(s[0..slash_pos])
}

function GetDenominator(s: string): int
    requires ValidFraction(s)
    ensures GetDenominator(s) > 0
{
    var slash_pos := FindSlash(s);
    StringToInt(s[slash_pos+1..])
}

function FindSlash(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == '/'
    ensures 0 <= FindSlash(s) < |s|
    ensures s[FindSlash(s)] == '/'
{
    FindSlashHelper(s, 0)
}

function StringToInt(s: string): int
{
    StringToIntHelper(s, 0)
}

function CharToInt(c: char): int
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}

// ======= HELPERS =======
function FindSlashHelper(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires exists i :: pos <= i < |s| && s[i] == '/'
    ensures pos <= FindSlashHelper(s, pos) < |s|
    ensures s[FindSlashHelper(s, pos)] == '/'
    decreases |s| - pos
{
    if pos < |s| && s[pos] == '/' then pos
    else FindSlashHelper(s, pos + 1)
}

function StringToIntHelper(s: string, acc: int): int
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + CharToInt(s[0]))
}

// ======= MAIN METHOD =======
method simplify(x: string, n: string) returns (result: bool)
    requires |x| > 0 && |n| > 0
    requires exists i :: 0 <= i < |x| && x[i] == '/'
    requires exists j :: 0 <= j < |n| && n[j] == '/'
    requires forall i :: 0 <= i < |x| ==> (x[i] == '/' || ('0' <= x[i] <= '9'))
    requires forall j :: 0 <= j < |n| ==> (n[j] == '/' || ('0' <= n[j] <= '9'))
    requires ValidFraction(x)
    requires ValidFraction(n)
    ensures result <==> (GetNumerator(x) * GetNumerator(n)) % (GetDenominator(x) * GetDenominator(n)) == 0
{
    // Find the '/' in x
    var x_slash_pos := 0;
    while x_slash_pos < |x| && x[x_slash_pos] != '/'
        invariant x_slash_pos <= |x|
    {
        x_slash_pos := x_slash_pos + 1;
    }

    // Find the '/' in n
    var n_slash_pos := 0;
    while n_slash_pos < |n| && n[n_slash_pos] != '/'
        invariant n_slash_pos <= |n|
    {
        n_slash_pos := n_slash_pos + 1;
    }

    // Extract parts
    var x_num_str := x[0..x_slash_pos];
    var x_den_str := x[x_slash_pos+1..];
    var n_num_str := n[0..n_slash_pos];
    var n_den_str := n[n_slash_pos+1..];

    // Convert to integers
    var x_num := StringToInt(x_num_str);
    var x_den := StringToInt(x_den_str);
    var n_num := StringToInt(n_num_str);
    var n_den := StringToInt(n_den_str);

    // Multiply fractions: (x_num/x_den) * (n_num/n_den) = (x_num * n_num) / (x_den * n_den)
    var result_num := x_num * n_num;
    var result_den := x_den * n_den;

    // Check if the result is a whole number (numerator divisible by denominator)
    result := result_num % result_den == 0;
}
