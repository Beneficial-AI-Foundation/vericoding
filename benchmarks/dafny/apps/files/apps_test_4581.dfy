Calculate the price of a bowl of ramen based on selected toppings.
Base price is 700 yen, each topping ('o') adds 100 yen.
Input is a 3-character string with 'o' (included) or 'x' (not included).

predicate ValidInput(s: string) {
    |s| == 3 && forall i :: 0 <= i < |s| ==> s[i] == 'o' || s[i] == 'x'
}

function countO(s: string): int
    ensures countO(s) >= 0
    ensures countO(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'o' then 1 else 0) + countO(s[1..])
}

function CalculatePrice(s: string): int
    requires ValidInput(s)
    ensures CalculatePrice(s) >= 700
    ensures CalculatePrice(s) == countO(s) * 100 + 700
{
    countO(s) * 100 + 700
}

function IntToString(n: int) : string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string) : string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else IntToStringHelper(n / 10, [((n % 10) + 48) as char] + acc)
}

lemma countOLemma(prefix: string, suffix: string)
    ensures countO(prefix + suffix) == countO(prefix) + countO(suffix)
{
    if |prefix| == 0 {
        assert prefix + suffix == suffix;
    } else {
        assert prefix == [prefix[0]] + prefix[1..];
        assert prefix + suffix == [prefix[0]] + (prefix[1..] + suffix);
        countOLemma(prefix[1..], suffix);
    }
}

method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == IntToString(CalculatePrice(s)) + "\n"
    ensures CalculatePrice(s) >= 700
{
    var count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == countO(s[..i])
    {
        assert s[..i+1] == s[..i] + [s[i]];
        countOLemma(s[..i], [s[i]]);
        assert countO(s[..i+1]) == countO(s[..i]) + (if s[i] == 'o' then 1 else 0);
        if s[i] == 'o' {
            count := count + 1;
        }
        i := i + 1;
    }
    assert s[..|s|] == s;
    assert count == countO(s);
    var value := count * 100 + 700;
    result := IntToString(value) + "\n";
}
