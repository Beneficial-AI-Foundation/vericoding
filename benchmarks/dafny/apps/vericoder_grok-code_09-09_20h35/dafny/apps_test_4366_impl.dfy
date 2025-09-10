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
function IntToString(n: int): string
    requires 0 <= n <= 23
{
    if n < 10 then ['0' + n as char]
    else ['0' + (n / 10) as char, '0' + (n % 10) as char]
}

function StringToInt(s: string): int
    requires |s| == 1 || |s| == 2
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then (s[0] as int - '0' as int)
    else (s[0] as int - '0' as int) * 10 + (s[1] as int - '0' as int)
}

lemma IntStringRoundTrip(n: int)
    requires 0 <= n <= 23
    ensures StringToInt(IntToString(n)) == n
{
    if n < 10 {
        calc == {
            StringToInt(IntToString(n));
            (('0' + n as char) as int - '0' as int);
            n;
        }
    } else {
        calc == {
            StringToInt(IntToString(n));
            (( '0' + (n / 10) as char) as int - '0' as int) * 10 + (( '0' + (n % 10) as char) as int - '0' as int);
            (n / 10) * 10 + (n % 10);
            n;
        }
    }
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
    var space_index := 0;
    while space_index < |input| && input[space_index] != ' '
        invariant 0 <= space_index <= |input|
        invariant forall k :: 0 <= k < space_index ==> input[k] != ' '
        invariant exists i :: space_index <= i < |input| && input[i] == ' '
        invariant forall j :: 0 <= j < space_index ==> '0' <= input[j] <= '9'
    {
        space_index := space_index + 1;
    }
    var a_str := input[..space_index];
    assert |a_str| == 1 || |a_str| == 2;
    assert forall i :: 0 <= i < |a_str| ==> '0' <= a_str[i] <= '9';
    var A := StringToInt(a_str);
    if |a_str| == 1 {
        assert A <= 9;
    } else {
        assert A >= 10;
    }
    assert 0 <= A <= 23;
    var b_start := space_index + 1;
    var b_end := |input|;
    var i := b_start;
    while i < |input| && input[i] != '\n'
        invariant b_start <= i <= |input|
        invariant forall k :: b_start <= k < i ==> '0' <= input[k] <= '9'
        invariant i <= b_start + 2
        decreases |input| - i
    {
        i := i + 1;
    }
    if i < |input| {
        b_end := i;
    }
    var b_str := input[b_start .. b_end];
    assert |b_str| == 1 || |b_str| == 2;
    assert forall i :: 0 <= i < |b_str| ==> '0' <= b_str[i] <= '9';
    var B := StringToInt(b_str);
    if |b_str| == 1 {
        assert B <= 9;
    } else {
        assert B >= 10;
    }
    assert 0 <= B <= 23;
    var start := ContestStartTime(A, B);
    result := IntToString(start) + "\n";
}
// </vc-code>

