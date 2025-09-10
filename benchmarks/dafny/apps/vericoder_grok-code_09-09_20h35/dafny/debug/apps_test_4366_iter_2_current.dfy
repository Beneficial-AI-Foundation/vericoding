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

function IndexOf(s: string, ch: char): int
    requires exists i :: 0 <= i < |s| && s[i] == ch
    ensures 0 <= IndexOf(s, ch) < |s| && s[IndexOf(s, ch)] == ch
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] != ch
    {
        if s[i] == ch
        {
            assert s[i] == ch;
            return i;
        }
        i := i + 1;
    }
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
    var space_index := IndexOf(input, ' ');
    var a_str := input[..space_index];
    var b_start := space_index + 1;
    var b_end := |input|;
    var i := b_start;
    while i < |input| && input[i] != '\n'
        decreases |input| - i
    {
        i := i + 1;
    }
    if i < |input| {
        b_end := i;
    }
    var b_str := input[b_start .. b_end];
    var A := StringToInt(a_str);
    var B := StringToInt(b_str);
    var start := ContestStartTime(A, B);
    result := IntToString(start) + "\n";
}
// </vc-code>

