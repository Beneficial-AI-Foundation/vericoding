// <vc-preamble>
predicate ValidInput(a: string, k: int) {
    |a| >= 1 && |a| <= 100000 && k >= 1 &&
    (forall i :: 0 <= i < |a| ==> a[i] >= '0' && a[i] <= '9')
}

function computeAnswer(a: string, k: int): int
  requires ValidInput(a, k)
  ensures 0 <= computeAnswer(a, k) < 1000000007
{
  var MOD := 1000000007;
  var n := |a|;
  var power_nk := modpow(2, n * k, MOD);
  var power_n := modpow(2, n, MOD);

  if power_n == 1 then 0
  else
    var numerator := (1 - power_nk + MOD) % MOD;
    var denominator := (1 - power_n + MOD) % MOD;
    var m := (numerator * modinv(denominator, MOD)) % MOD;

    computeSum(a, m, |a| - 1)
}

function computeSum(a: string, m: int, pos: int): int
  requires 0 <= m < 1000000007
  requires -1 <= pos < |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= '0' && a[i] <= '9'
  ensures 0 <= computeSum(a, m, pos) < 1000000007
  decreases pos + 1
{
  var MOD := 1000000007;
  if pos < 0 then 0
  else if a[pos] == '0' || a[pos] == '5' then
    var power_pos := modpow(2, pos, MOD);
    var contribution := (m * power_pos) % MOD;
    var rest := computeSum(a, m, pos - 1);
    (contribution + rest) % MOD
  else
    computeSum(a, m, pos - 1)
}
// </vc-preamble>

// <vc-helpers>
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else 
        var pos := findNewline(s, 0);
        if pos == -1 then [s]
        else if pos < |s| then [s[0..pos]] + splitLines(s[pos+1..])
        else if pos == |s| then [s[0..pos]]
        else []
}

function findNewline(s: string, start: int): int
  requires 0 <= start <= |s|
  ensures -1 <= findNewline(s, start) <= |s|
  decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else findNewline(s, start + 1)
}

function parseInt(s: string): int
{
    if |s| == 0 then 0
    else parseIntHelper(s, 0, 0)
}

function parseIntHelper(s: string, pos: int, acc: int): int
  requires acc >= 0
  requires 0 <= pos <= |s|
  decreases |s| - pos
{
    if pos >= |s| then acc
    else if s[pos] >= '0' && s[pos] <= '9' then
        parseIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
    else acc
}

function intToString(n: int): string
  requires n >= 0
{
    if n == 0 then "0"
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
    if n == 0 then acc
    else intToStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
}

function modpow(base: int, exp: int, mod: int): int
  requires mod > 1
  requires exp >= 0
  ensures 0 <= modpow(base, exp, mod) < mod
{
    if exp <= 0 then 1
    else if exp % 2 == 0 then
        var half := modpow(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * modpow(base, exp - 1, mod)) % mod
}

function modinv(a: int, mod: int): int
  requires mod > 1
  requires a % mod != 0
  ensures 0 <= modinv(a, mod) < mod
{
    modpow(a, mod - 2, mod)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  ensures |result| > 0
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| >= 2) ==> 
      (exists num: int :: 0 <= num < 1000000007 && result == intToString(num) + "\n")
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| < 2) ==> result == "0\n"
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| >= 2 && 
    (parseInt(lines[1]) < 1 || |lines[0]| < 1 || |lines[0]| > 100000)) ==> result == "0\n"
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| >= 2 && 
    (exists i :: 0 <= i < |lines[0]| && !(lines[0][i] >= '0' && lines[0][i] <= '9'))) ==> result == "0\n"
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| >= 2 && 
    ValidInput(lines[0], parseInt(lines[1]))) ==> 
      (exists num: int :: 0 <= num < 1000000007 && result == intToString(num) + "\n" &&
      num == computeAnswer(lines[0], parseInt(lines[1])))
  ensures forall lines: seq<string> :: 
    (lines == splitLines(stdin_input) && |lines| >= 2 && 
    ValidInput(lines[0], parseInt(lines[1])) &&
    modpow(2, |lines[0]|, 1000000007) == 1) ==> result == "0\n"
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(stdin_input);

    if |lines| < 2 {
        result := "0\n";
        return;
    }

    var a := lines[0];
    var k_str := lines[1];
    var k := parseInt(k_str);

    if k < 1 || |a| < 1 || |a| > 100000 {
        result := "0\n";
        assert 0 <= 0 < 1000000007 && result == intToString(0) + "\n";
        return;
    }

    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j] >= '0' && a[j] <= '9'
    {
        if !(a[i] >= '0' && a[i] <= '9') {
            result := "0\n";
            assert exists idx :: 0 <= idx < |lines[0]| && !(lines[0][idx] >= '0' && lines[0][idx] <= '9');
            assert 0 <= 0 < 1000000007 && result == intToString(0) + "\n";
            return;
        }
        i := i + 1;
    }

    assert forall j :: 0 <= j < |a| ==> a[j] >= '0' && a[j] <= '9';
    assert ValidInput(a, k);

    var n := |a|;
    var MOD := 1000000007;

    var power_nk := modpow(2, n * k, MOD);
    var power_n := modpow(2, n, MOD);

    var numerator := (1 - power_nk + MOD) % MOD;
    var denominator := (1 - power_n + MOD) % MOD;

    if denominator == 0 {
        result := "0\n";
        assert modpow(2, |lines[0]|, 1000000007) == 1;
        assert 0 <= 0 < 1000000007 && result == intToString(0) + "\n";
        return;
    }

    var m := (numerator * modinv(denominator, MOD)) % MOD;

    var ans := 0;
    var j := n - 1;
    while j >= 0 
        invariant -1 <= j < n
        invariant 0 <= ans < MOD
        invariant ans == (computeSum(a, m, n - 1) - computeSum(a, m, j)) % MOD
        invariant forall idx :: 0 <= idx < |a| ==> a[idx] >= '0' && a[idx] <= '9'
    {
        if a[j] == '0' || a[j] == '5' {
            var power_j := modpow(2, j, MOD);
            ans := (ans + (m * power_j) % MOD) % MOD;
        }
        j := j - 1;
    }

    ans := (ans % MOD + MOD) % MOD;
    assert ans == computeSum(a, m, n - 1);
    assert ans == computeAnswer(lines[0], parseInt(lines[1]));
    assert 0 <= ans < 1000000007 && result == intToString(ans) + "\n";
    result := intToString(ans) + "\n";
}
// </vc-code>
