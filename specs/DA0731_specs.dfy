// <vc-preamble>
predicate ValidBracketString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

function CountOpenBrackets(s: string, upTo: int): int
    requires 0 <= upTo < |s|
    requires ValidBracketString(s)
{
    if upTo == 0 then
        if s[0] == '(' then 1 else 0
    else
        CountOpenBrackets(s, upTo - 1) + (if s[upTo] == '(' then 1 else 0)
}

function CountCloseBrackets(s: string, from: int): int
    requires 0 <= from < |s|
    requires ValidBracketString(s)
    decreases |s| - from
{
    if from == |s| - 1 then
        if s[from] == ')' then 1 else 0
    else
        (if s[from] == ')' then 1 else 0) + CountCloseBrackets(s, from + 1)
}

function CountRSBSSubsequencesSpec(s: string): int
    requires ValidBracketString(s)
{
    CountRSBSSubsequences(s)
}

function CountRSBSSubsequences(s: string): int
    requires ValidBracketString(s)
{
    var m := 1000000007;
    var n := |s|;
    if n == 0 then 0
    else
        SumOverOpenPositions(s, 0, m)
}

function SumOverOpenPositions(s: string, pos: int, mod: int): int
    requires ValidBracketString(s)
    requires 0 <= pos <= |s|
    requires mod >= 2
    decreases |s| - pos
{
    if pos >= |s| then 0
    else if s[pos] == '(' then
        var openCount := CountOpenBrackets(s, pos);
        var closeCount := CountCloseBrackets(s, pos);
        var contribution := if openCount > 0 && closeCount > 0 then
            BinomialCoeffMod(openCount + closeCount - 1, openCount, mod)
        else 0;
        (contribution + SumOverOpenPositions(s, pos + 1, mod)) % mod
    else
        SumOverOpenPositions(s, pos + 1, mod)
}
// </vc-preamble>

// <vc-helpers>
function pow(base: int, exp: int, mod: int): int
    requires mod > 0
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1
    else if exp % 2 == 0 then
        var half := pow(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * pow(base, exp - 1, mod)) % mod
}

function Factorial(n: int): int
    requires n >= 0
    decreases n
{
    if n == 0 then 1
    else n * Factorial(n - 1)
}

function BinomialCoeffMod(n: int, k: int, mod: int): int
    requires n >= 0 && k >= 0 && k <= n
    requires mod >= 2
{
    if k == 0 || k == n then 1 % mod
    else if n == 0 then 0
    else
        var facN := Factorial(n) % mod;
        var facK := Factorial(k) % mod;
        var facNK := Factorial(n - k) % mod;
        var invK := pow(facK, mod - 2, mod);
        var invNK := pow(facNK, mod - 2, mod);
        (((facN * invK) % mod) * invNK) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidBracketString(s)
    requires |s| <= 200000
    ensures 0 <= result < 1000000007
    ensures result == CountRSBSSubsequencesSpec(s)
// </vc-spec>
// <vc-code>
{
    var m := 1000000007;
    var n := |s|;

    if n == 0 {
        return 0;
    }

    var o := new int[n];
    var c := new int[n];
    var fac := new int[2*n + 1];

    fac[0] := 1;
    var i := 1;
    while i <= 2*n
        invariant 1 <= i <= 2*n + 1
        invariant forall j :: 0 <= j < i ==> fac[j] >= 0
    {
        fac[i] := (fac[i-1] * i) % m;
        i := i + 1;
    }

    var invfac := new int[2*n + 1];
    i := 0;
    while i <= 2*n
        invariant 0 <= i <= 2*n + 1
    {
        invfac[i] := pow(fac[i], m-2, m);
        i := i + 1;
    }

    if s[0] == '(' {
        o[0] := 1;
    } else {
        o[0] := 0;
    }
    assert o[0] == CountOpenBrackets(s, 0);

    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> o[j] == CountOpenBrackets(s, j)
    {
        if s[i] == '(' {
            o[i] := o[i-1] + 1;
        } else {
            o[i] := o[i-1];
        }
        i := i + 1;
    }

    assert forall j :: 0 <= j < n ==> o[j] == CountOpenBrackets(s, j);

    if s[n-1] == ')' {
        c[n-1] := 1;
    } else {
        c[n-1] := 0;
    }

    i := n-2;
    while i >= 0
        invariant -1 <= i <= n-2
        invariant forall j :: i < j < n ==> c[j] == CountCloseBrackets(s, j)
    {
        if s[i] == ')' {
            c[i] := c[i+1] + 1;
        } else {
            c[i] := c[i+1];
        }
        i := i - 1;
    }

    assert forall j :: 0 <= j < n ==> c[j] == CountCloseBrackets(s, j);

    var ans := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= ans < m
        invariant ans == SumOverOpenPositions(s, 0, m) - SumOverOpenPositions(s, i, m)
    {
        if s[i] == '(' {
            var a := o[i];
            var b := c[i];
            if a > 0 && b > 0 && a + b - 1 <= 2*n && a <= 2*n && b - 1 <= 2*n {
                var term := (((fac[a+b-1] * invfac[a]) % m) * invfac[b-1]) % m;
                ans := (ans + term) % m;
            }
        }
        i := i + 1;
    }

    return ans;
}
// </vc-code>
