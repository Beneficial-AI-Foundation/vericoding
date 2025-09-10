predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
function IntToString(i: int): string
    requires 0 <= i // reasonable upper bound. A number like 999999999999999999 for max int is fine for practical purposes, but for an int we need to handle its full range. Let's make it simpler here assuming non-negative for this problem.
    ensures var s := i as string; forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
{
    if i == 0 then "0"
    else
        var s := "";
        var temp := i;
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
            invariant i > 0 ==> (s == "" && temp == i) || (i == (temp * Pow10(|s|) + ParseInt(s)))
            decreasing temp
        {
            s := ('0' + (temp % 10)) + s;
            temp := temp / 10;
        }
        s
}
function ParseInt(s: string): (i: int)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0
    ensures i == (var res := 0; for k := 0 to |s|-1 { res := res * 10 + (s[k] - '0'); } return res;)
{
    var res := 0;
    for k := 0 to |s|-1
        invariant res >= 0
        invariant k <= |s|
        invariant forall j :: 0 <= j < k ==> '0' <= s[j] <= '9'
        invariant res == (var r := 0; for x := 0 to k-1 { r := r * 10 + (s[x] - '0'); } return r;)
    {
        res := res * 10 + (s[k] - '0');
    }
    return res;
}

lemma ParseIntIntToString(i: int)
    requires 0 <= i
    ensures ParseInt(IntToString(i)) == i
{
    if i == 0 {
        assert ParseInt("0") == 0;
    } else {
        var s := "";
        var temp := i;
        var p := 0; // power of 10
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
            invariant i == temp * Pow10(p) + (if s == "" then 0 else ParseInt(s))
            invariant p == |s|
            decreasing temp
        {
            s := ('0' + (temp % 10)) + s;
            temp := temp / 10;
            p := p + 1;
        }
        assert i == ParseInt(s);
    }
}

lemma IntToStringParseInt(s: string)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0
    ensures IntToString(ParseInt(s)) == s
{
    var i := ParseInt(s);
    if i == 0 {
        assert s == "0";
    } else {
        var temp := i;
        var res_s := "";
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |res_s| ==> '0' <= res_s[k] <= '9'
            invariant i == temp * Pow10(|res_s|) + (if res_s == "" then 0 else ParseInt(res_s))
            invariant i == ParseInt(s) ==> IntToString(ParseInt(s)) == s
            decreasing temp
        {
            res_s := ('0' + (temp % 10)) + res_s;
            temp := temp / 10;
        }
        assert IntToString(ParseInt(s)) == res_s;
        assert res_s == s;
    }
}

function Pow10(exp: nat): int
    ensures Pow10(exp) > 0
{
    if exp == 0 then 1
    else 10 * Pow10(exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var parts := input.Split(' ').ToSequence();
    var A_str: string;
    var B_str: string;
    var inputWithoutNewline: string;

    if input[|input|-1] == '\n' {
        inputWithoutNewline := input[..|input|-1];
    } else {
        inputWithoutNewline := input;
    }
    
    var partsWithoutNewline := inputWithoutNewline.Split(' ').ToSequence();
    A_str := partsWithoutNewline[0];
    B_str := partsWithoutNewline[1];

    // Assert that A_str and B_str are digits only
    assert forall k :: 0 <= k < |A_str| ==> '0' <= A_str[k] <= '9';
    assert forall k :: 0 <= k < |B_str| ==> '0' <= B_str[k] <= '9';

    var A := ParseInt(A_str);
    var B := ParseInt(B_str);

    ParseIntIntToString(A);
    ParseIntIntToString(B);

    assert (inputWithoutNewline == IntToString(A) + " " + IntToString(B));

    assert 0 <= A <= 23;
    assert 0 <= B <= 23;

    var contest_start_time := ContestStartTime(A, B);
    result := IntToString(contest_start_time) + "\n";
}
// </vc-code>

