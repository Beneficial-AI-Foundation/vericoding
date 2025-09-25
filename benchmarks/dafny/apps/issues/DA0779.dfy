// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 &&
    (input[|input|-1] == '\n' ==> |input| > 1) && 
    (input[|input|-1] == '\n' ==> forall i :: 0 <= i < |input|-1 ==> '0' <= input[i] <= '9') &&
    (input[|input|-1] != '\n' ==> forall i :: 0 <= i < |input| ==> '0' <= input[i] <= '9')
}

predicate ValidOutput(result: string)
{
    |result| > 0 && result[|result|-1] == '\n'
}

function computeAlgorithmResult(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures computeAlgorithmResult(s) >= 0
    ensures computeAlgorithmResult(s) < 1000000007
{
    var M := 1000000007;
    computeAlgorithmResultHelper(s, 0, 0, 0, 0, |s|, M)
}

function computeAlgorithmResultHelper(s: string, i: int, o: int, u: int, v: int, n: int, M: int): int
    requires 0 <= i <= n <= |s|
    requires M == 1000000007
    requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    requires 0 <= u 
    requires 0 <= v < M
    ensures computeAlgorithmResultHelper(s, i, o, u, v, n, M) >= 0
    ensures computeAlgorithmResultHelper(s, i, o, u, v, n, M) < M
    decreases n - i
{
    if i >= n then o % M
    else
        var c := s[i] as int - '0' as int;
        var new_u := u + v;
        var new_v := (10 * v + c) % M;
        var power := pow(10, n - i - 1, M);
        var contribution := power * ((i * i + i) / 2 * c + new_u);
        var new_o := o + contribution;
        computeAlgorithmResultHelper(s, i + 1, new_o, new_u, new_v, n, M)
}
// </vc-preamble>

// <vc-helpers>
function stringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures stringToInt(s) >= 0
    ensures |s| == 0 ==> stringToInt(s) == 0
{
    if |s| == 0 then 0
    else stringToIntHelper(s, 0, 0)
}

function stringToIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires acc >= 0
    ensures stringToIntHelper(s, index, acc) >= 0
    decreases |s| - index
{
    if index >= |s| then acc
    else 
        var digit := s[index] as int - '0' as int;
        stringToIntHelper(s, index + 1, acc * 10 + digit)
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures forall i :: 0 <= i < |intToString(n)| ==> '0' <= intToString(n)[i] <= '9'
    ensures n == 0 ==> intToString(n) == "0"
    ensures n > 0 ==> |intToString(n)| >= 1
{
    if n == 0 then "0"
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
    requires n > 0
    requires forall i :: 0 <= i < |acc| ==> '0' <= acc[i] <= '9'
    ensures |intToStringHelper(n, acc)| > 0
    ensures forall i :: 0 <= i < |intToStringHelper(n, acc)| ==> '0' <= intToStringHelper(n, acc)[i] <= '9'
    decreases n
{
    if n < 10 then 
        var digit := ('0' as int + n) as char;
        [digit] + acc
    else 
        var digit := ('0' as int + n % 10) as char;
        intToStringHelper(n / 10, [digit] + acc)
}

function pow(base: int, exp: int, mod: int): int
    requires mod > 0
    requires exp >= 0
    ensures 0 <= pow(base, exp, mod) < mod
    ensures mod == 1 ==> pow(base, exp, mod) == 0
    decreases exp
{
    if exp == 0 then 1 % mod
    else if exp % 2 == 0 then
        var half := pow(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * pow(base, exp - 1, mod)) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures computeAlgorithmResult(if input[|input|-1] == '\n' then input[..|input|-1] else input) < 1000000007
// </vc-spec>
// <vc-code>
{
    var s := if input[|input|-1] == '\n' then input[..|input|-1] else input;
    var M := 1000000007;
    var o := 0;
    var u := 0;
    var v := 0;
    var n := |s|;

    for i := 0 to n
        invariant 0 <= o
        invariant 0 <= u
        invariant 0 <= v < M
    {
        var c := s[i] as int - '0' as int;
        u := u + v;
        v := (10 * v + c) % M;
        var power := pow(10, n - i - 1, M);
        var contribution := power * ((i * i + i) / 2 * c + u);
        o := o + contribution;
    }

    var final_result := o % M;
    var value_str := intToString(final_result);
    result := value_str + "\n";
}
// </vc-code>
