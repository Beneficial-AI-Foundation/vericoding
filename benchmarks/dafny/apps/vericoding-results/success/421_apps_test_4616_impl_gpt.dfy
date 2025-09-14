predicate ValidInput(s: string)
{
    |s| >= 3 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidAbbreviation(s: string, result: string)
{
    |result| >= 3 &&
    |s| >= 3 &&
    result[0] == s[0] &&
    result[|result|-1] == s[|s|-1] &&
    result == [s[0]] + IntToString(|s| - 2) + [s[|s|-1]]
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}

// <vc-helpers>
lemma lemma_IntToStringHelper_len(n: int) returns (k: nat)
    requires n >= 0
    ensures k == |IntToStringHelper(n)|
    ensures n > 0 ==> k >= 1
    decreases n
{
    if n == 0 {
        k := 0;
    } else {
        var k0 := lemma_IntToStringHelper_len(n / 10);
        k := k0 + 1;
    }
}

lemma lemma_IntToString_len_ge1(n: int)
    requires n >= 1
    ensures |IntToString(n)| >= 1
{
    var k := lemma_IntToStringHelper_len(n);
    assert |IntToString(n)| == |IntToStringHelper(n)|;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidAbbreviation(s, result)
// </vc-spec>
// <vc-code>
{
  var n := |s| - 2;
  lemma_IntToString_len_ge1(n);
  result := [s[0]] + IntToString(n) + [s[|s|-1]];
}
// </vc-code>

