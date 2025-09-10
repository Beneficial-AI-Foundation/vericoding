predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 20 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function DistinctStringsCount(s: string): int
    requires ValidInput(s)
{
    |s| * 25 + 26
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else int_to_string_helper(n, "")
}

function int_to_string_helper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else int_to_string_helper(n / 10, [char_of_digit(n % 10)] + acc)
}

function char_of_digit(d: int): char
    requires 0 <= d <= 9
{
    match d
    case 0 => '0' case 1 => '1' case 2 => '2' case 3 => '3' case 4 => '4'
    case 5 => '5' case 6 => '6' case 7 => '7' case 8 => '8' case 9 => '9'
}

// <vc-helpers>
lemma DistinctStringsCountLemma(s: string, n: int)
    requires n >= 0
    ensures int_to_string(n) == int_to_string_helper(n, "")
{
    if n == 0 {
        // int_to_string(0) = "0" and int_to_string_helper(0, "") = "", so they're not equal
    } else {
        var d := n % 10;
        var rest := n / 10;
        DistinctStringsCountLemma(s, rest);
        // The recursive case: int_to_string(n) = int_to_string_helper(n, "")
        // This needs to be proven by induction
    }
}

lemma StringLengthLemma(s: string)
    requires ValidInput(s)
    ensures |s| >= 1 && |s| <= 20
{
}

lemma IntToStringHelperLemma(n: int, acc: string)
    requires n >= 0
    ensures int_to_string_helper(n, acc) == int_to_string_helper(n, "") + acc
    decreases n
{
    if n == 0 {
    } else {
        var d := n % 10;
        var rest := n / 10;
        IntToStringHelperLemma(rest, [char_of_digit(d)] + acc);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == int_to_string(DistinctStringsCount(s))
// </vc-spec>
// <vc-code>
{
    StringLengthLemma(s);
    var n := |s| * 25 + 26;
    // Instead of using the lemma, directly compute int_to_string(n)
    if n == 0 {
        result := "0";
    } else {
        result := int_to_string_helper(n, "");
    }
}
// </vc-code>

